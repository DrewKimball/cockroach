package main

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
)

// checkTableScans detects problematic table scans
func (a *Analyzer) checkTableScans(planTree *PlanTree) []AnalysisResult {
	var results []AnalysisResult

	// Find all scan nodes
	scans := planTree.Root.FindNodes(func(n *PlanNode) bool {
		return n.Operator == "scan"
	})

	for _, scan := range scans {
		table, index := scan.GetTableAndIndex()
		if table == "" {
			continue
		}

		rows := scan.GetRowCount()
		isFullScan := scan.IsFullScan()
		kvTime := scan.GetKVTime()
		cpuTime := scan.GetCPUTime()
		contentionTime := scan.GetContentionTime()

		// Only flag scans with high row counts or significant time
		if rows > 1000 || kvTime > 1.0 {
			severity := "warning"
			message := fmt.Sprintf("Large scan on %s@%s (~%s rows)", table, index, formatNumber(rows))

			if rows > 100000 || kvTime > 5.0 {
				severity = "critical"
			}

			suggestion := "Consider adding an index to support the query filters, or add constraints to limit the scan. Use CREATE INDEX to add appropriate indexes on filtered columns."

			// Provide more specific messaging if this is a full scan
			if isFullScan {
				message = fmt.Sprintf("Full scan on %s@%s (~%s rows)", table, index, formatNumber(rows))
				suggestion = "Full scan detected. Consider adding WHERE clause constraints to limit the rows scanned, or add an index that better matches the query filters."
			}

			results = append(results, AnalysisResult{
				Severity:       severity,
				Category:       "scan",
				Message:        message,
				Suggestion:     suggestion,
				KVTime:         kvTime,
				CPUTime:        cpuTime,
				ContentionTime: contentionTime,
				Details: map[string]interface{}{
					"table":          table,
					"index":          index,
					"estimated_rows": rows,
					"full_scan":      isFullScan,
				},
			})
		}
	}

	return results
}

// checkJoins detects inefficient join operations
func (a *Analyzer) checkJoins(planTree *PlanTree) []AnalysisResult {
	var results []AnalysisResult

	// Find cross join nodes
	crossJoins := planTree.Root.FindNodes(func(n *PlanNode) bool {
		return strings.Contains(strings.ToLower(n.Operator), "cross join")
	})

	for range crossJoins {
		results = append(results, AnalysisResult{
			Severity:   "critical",
			Category:   "join",
			Message:    "Cross join detected (Cartesian product)",
			Suggestion: "Cross joins create Cartesian products and are usually unintentional. Add appropriate JOIN conditions or WHERE clauses.",
			Details: map[string]interface{}{
				"join_type": "cross",
			},
		})
	}

	// Note: Hash joins are not inherently problematic and are often optimal.
	// We could add more sophisticated analysis here to detect large hash joins
	// by examining row counts, but simply detecting "hash join" is not useful.

	return results
}

// checkIndexJoins detects expensive index joins
func (a *Analyzer) checkIndexJoins(planTree *PlanTree) []AnalysisResult {
	var results []AnalysisResult

	// Find all index join nodes
	indexJoins := planTree.Root.FindNodes(func(n *PlanNode) bool {
		return strings.Contains(strings.ToLower(n.Operator), "index join")
	})

	for _, indexJoin := range indexJoins {
		table, index := indexJoin.GetTableAndIndex()
		rows := indexJoin.GetRowCount()
		kvTime := indexJoin.GetKVTime()
		cpuTime := indexJoin.GetCPUTime()
		contentionTime := indexJoin.GetContentionTime()

		// Check if this is expensive based on absolute KV time or row count
		// Note: We'll compare to total execution time later at the reporting level
		isExpensive := (kvTime > 1.0) || (rows > 10000)

		if isExpensive {
			suggestion := "Consider adding filtered columns to the index to avoid the index join"

			// Try to enhance suggestion with schema analysis
			if table != "" && index != "" {
				if enhanced := a.enhanceIndexJoinSuggestion(table, index); enhanced != "" {
					suggestion = enhanced
				}
			}

			severity := "warning"
			if kvTime > 5.0 || rows > 50000 {
				severity = "critical"
			}

			timeDesc := ""
			if kvTime > 0 {
				timeDesc = fmt.Sprintf(" (%.2fs KV time)", kvTime)
			}

			results = append(results, AnalysisResult{
				Severity:       severity,
				Category:       "index_join",
				Message:        fmt.Sprintf("Expensive index join on %s%s", table, timeDesc),
				Suggestion:     suggestion,
				KVTime:         kvTime,
				CPUTime:        cpuTime,
				ContentionTime: contentionTime,
				Details: map[string]interface{}{
					"table":          table,
					"index_used":     index,
					"rows_processed": rows,
				},
			})
		}
	}

	return results
}

// enhanceIndexJoinSuggestion provides enhanced suggestions based on schema analysis
func (a *Analyzer) enhanceIndexJoinSuggestion(tableName, indexName string) string {
	statementPath := filepath.Join(a.extractedDir, "statement.sql")

	statementContent, err := os.ReadFile(statementPath)

	if err != nil {
		return ""
	}

	statement := string(statementContent)

	// Extract WHERE clause columns
	whereRegex := regexp.MustCompile(`(?i)WHERE\s+(.+?)(?:\s+ORDER\s+BY|\s+LIMIT|\s+GROUP\s+BY|$)`)
	whereMatch := whereRegex.FindStringSubmatch(statement)

	var whereColumns []string
	if whereMatch != nil {
		whereClause := whereMatch[1]
		colRegex := regexp.MustCompile(`\b([a-zA-Z_]\w*)\s*[<>=!]`)
		colMatches := colRegex.FindAllStringSubmatch(whereClause, -1)
		for _, match := range colMatches {
			whereColumns = append(whereColumns, match[1])
		}
	}

	// Extract SELECT columns
	selectRegex := regexp.MustCompile(`(?i)SELECT\s+(.+?)\s+FROM`)
	selectMatch := selectRegex.FindStringSubmatch(statement)

	var selectCols []string
	hasSelectAll := false
	if selectMatch != nil {
		selectClause := selectMatch[1]
		if strings.Contains(selectClause, "*") {
			hasSelectAll = true
		} else {
			selectCols = strings.Split(selectClause, ",")
			for i, col := range selectCols {
				selectCols[i] = strings.TrimSpace(col)
			}
		}
	}

	if len(whereColumns) > 0 || len(selectCols) > 0 || hasSelectAll {
		suggestion := fmt.Sprintf("Add columns to index %s to avoid index join. ", indexName)
		if len(whereColumns) > 0 {
			suggestion += fmt.Sprintf("Consider including WHERE clause columns (%s) ", strings.Join(whereColumns, ", "))
		}
		if hasSelectAll {
			suggestion += "or frequently accessed columns as STORING columns. "
		}
		suggestion += fmt.Sprintf("Example: CREATE INDEX %s_enhanced ON %s (", indexName, tableName)

		// Add index key columns
		if len(whereColumns) > 0 {
			suggestion += strings.Join(whereColumns, ", ")
		} else {
			suggestion += "key_column"
		}
		suggestion += ")"

		// Add STORING clause for SELECT * or specific columns
		if hasSelectAll {
			suggestion += " STORING (other_columns)"
		} else if len(selectCols) > 0 {
			suggestion += fmt.Sprintf(" STORING (%s)", strings.Join(selectCols, ", "))
		}

		return suggestion
	}

	return ""
}

// checkSorts detects expensive sort operations
func (a *Analyzer) checkSorts(planTree *PlanTree) []AnalysisResult {
	var results []AnalysisResult

	// Find all sort nodes
	sorts := planTree.Root.FindNodes(func(n *PlanNode) bool {
		return n.Operator == "sort"
	})

	for _, sort := range sorts {
		rows := sort.GetRowCount()
		kvTime := sort.GetKVTime()
		cpuTime := sort.GetCPUTime()
		contentionTime := sort.GetContentionTime()

		// Only flag sorts on significant row counts
		if rows > 10000 {
			severity := "warning"
			if rows > 100000 {
				severity = "critical"
			}

			results = append(results, AnalysisResult{
				Severity:       severity,
				Category:       "sort",
				Message:        fmt.Sprintf("Sort operation on ~%s rows", formatNumber(rows)),
				Suggestion:     "Sorting large result sets can be expensive. Consider adding an index on the ORDER BY columns to avoid the sort operation, or use LIMIT to reduce rows sorted.",
				KVTime:         kvTime,
				CPUTime:        cpuTime,
				ContentionTime: contentionTime,
				Details: map[string]interface{}{
					"estimated_rows": rows,
				},
			})
			// Only report once
			break
		}
	}

	return results
}

// formatNumber formats a number with commas for readability
func formatNumber(n int) string {
	if n == 0 {
		return "0"
	}

	str := fmt.Sprintf("%d", n)
	if len(str) <= 3 {
		return str
	}

	var result []string
	for i, char := range str {
		if i > 0 && (len(str)-i)%3 == 0 {
			result = append(result, ",")
		}
		result = append(result, string(char))
	}

	return strings.Join(result, "")
}
