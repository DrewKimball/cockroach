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
	totalTime := planTree.GetTotalExecutionTime()

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

		// Calculate percentage of total time
		var timePercentage float64
		if totalTime > 0 && kvTime > 0 {
			timePercentage = (kvTime / totalTime) * 100
		}

		// Only flag scans with high row counts or significant time
		if rows > 1000 || kvTime > 1.0 || timePercentage > 10.0 {
			// Check if there are upstream filters or joins that could help constrain this scan
			hasUpstreamFilter := hasUpstreamFilterOrJoin(scan)

			message := fmt.Sprintf("Large scan on %s@%s (~%s rows)", table, index, formatNumber(rows))
			suggestion := "Consider adding an index to support the query filters, or add constraints to limit the scan."

			// Provide more specific messaging based on analysis
			if isFullScan {
				message = fmt.Sprintf("Full scan on %s@%s (~%s rows)", table, index, formatNumber(rows))
				suggestion = "Full scan detected. Consider adding WHERE clause constraints or an index that matches query filters."
			}

			if hasUpstreamFilter {
				message += " with upstream filter"
				suggestion = "This scan has filters applied afterward. Consider pushing filters down to the scan by creating an index on filtered columns, or converting to a lookup join if joining with another table."
			}

			// Add time information
			if kvTime > 0 {
				message += fmt.Sprintf(" (%.2fs KV time", kvTime)
				if timePercentage > 0 {
					message += fmt.Sprintf(", %.1f%% of total", timePercentage)
				}
				message += ")"
			}

			results = append(results, AnalysisResult{
				Category:       "scan",
				Message:        message,
				Suggestion:     suggestion,
				KVTime:         kvTime,
				CPUTime:        cpuTime,
				ContentionTime: contentionTime,
				Details: map[string]interface{}{
					"table":            table,
					"index":            index,
					"estimated_rows":   rows,
					"full_scan":        isFullScan,
					"upstream_filter":  hasUpstreamFilter,
					"time_percentage":  timePercentage,
				},
			})
		}
	}

	return results
}

// hasUpstreamFilterOrJoin checks if there are filter or join nodes upstream of this scan
func hasUpstreamFilterOrJoin(scan *PlanNode) bool {
	// Walk up the tree from the scan node
	current := scan.Parent
	for current != nil {
		op := strings.ToLower(current.Operator)

		// Check for filter operators
		if strings.Contains(op, "filter") {
			return true
		}

		// Check for selective join operators (hash join, merge join, lookup join)
		// that might have selectivity that could be pushed down
		if strings.Contains(op, "join") && !strings.Contains(op, "index join") {
			// Only flag if the join has a filter condition
			if current.GetAttribute("pred") != "" || current.GetAttribute("equality") != "" {
				return true
			}
		}

		current = current.Parent
	}
	return false
}

// checkJoins detects inefficient join operations
func (a *Analyzer) checkJoins(planTree *PlanTree) []AnalysisResult {
	var results []AnalysisResult
	totalTime := planTree.GetTotalExecutionTime()

	// Find cross join nodes
	crossJoins := planTree.Root.FindNodes(func(n *PlanNode) bool {
		return strings.Contains(strings.ToLower(n.Operator), "cross join")
	})

	for range crossJoins {
		results = append(results, AnalysisResult{
			Category:   "join",
			Message:    "Cross join detected (Cartesian product)",
			Suggestion: "Cross joins create Cartesian products and are usually unintentional. Add appropriate JOIN conditions or WHERE clauses.",
			Details: map[string]interface{}{
				"join_type": "cross",
			},
		})
	}

	// Find all join nodes (hash join, merge join, lookup join)
	allJoins := planTree.Root.FindNodes(func(n *PlanNode) bool {
		op := strings.ToLower(n.Operator)
		return (strings.Contains(op, "hash join") ||
			strings.Contains(op, "merge join") ||
			strings.Contains(op, "lookup join")) &&
			!strings.Contains(op, "index join")
	})

	for _, join := range allJoins {
		// Check for cardinality blowup: output rows >> input rows
		outputRows := join.GetRowCount()
		if outputRows == 0 {
			continue
		}

		// Get input row counts from children
		var inputRows int
		for _, child := range join.Children {
			childRows := child.GetRowCount()
			if childRows > inputRows {
				inputRows = childRows
			}
		}

		if inputRows == 0 {
			continue
		}

		// Calculate blowup factor
		blowupFactor := float64(outputRows) / float64(inputRows)

		// Flag if output is significantly larger than largest input (>5x)
		// This suggests poor join ordering or missing filters
		if blowupFactor > 5.0 && outputRows > 10000 {
			kvTime := join.GetKVTime()
			cpuTime := join.GetCPUTime()

			var timePercentage float64
			if totalTime > 0 && kvTime > 0 {
				timePercentage = (kvTime / totalTime) * 100
			}

			message := fmt.Sprintf("Join producing large intermediate result: %s output rows from %s input rows (%.1fx blowup)",
				formatNumber(outputRows), formatNumber(inputRows), blowupFactor)

			if kvTime > 0 {
				message += fmt.Sprintf(" (%.2fs", kvTime)
				if timePercentage > 0 {
					message += fmt.Sprintf(", %.1f%% of total", timePercentage)
				}
				message += ")"
			}

			results = append(results, AnalysisResult{
				Category:   "join",
				Message:    message,
				Suggestion: "Large intermediate result from join. Consider reordering joins to reduce intermediate cardinality, or adding more selective filters earlier in the query plan.",
				KVTime:     kvTime,
				CPUTime:    cpuTime,
				Details: map[string]interface{}{
					"join_type":       join.Operator,
					"output_rows":     outputRows,
					"input_rows":      inputRows,
					"blowup_factor":   blowupFactor,
					"time_percentage": timePercentage,
				},
			})
		}
	}

	return results
}

// checkIndexJoins detects expensive index joins
func (a *Analyzer) checkIndexJoins(planTree *PlanTree) []AnalysisResult {
	var results []AnalysisResult

	totalTime := planTree.GetTotalExecutionTime()

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

		// Calculate percentage of total time spent in this index join
		var timePercentage float64
		if totalTime > 0 && kvTime > 0 {
			timePercentage = (kvTime / totalTime) * 100
		}

		// Flag if it takes >10% of total time OR has high absolute time/rows
		// This surfaces index joins that are a significant fraction of execution
		isExpensive := (timePercentage > 10.0) || (kvTime > 1.0) || (rows > 10000)

		if isExpensive {
			suggestion := "Consider creating a covering index that includes the retrieved columns to eliminate the index join"

			// Try to enhance suggestion with schema analysis
			if table != "" && index != "" {
				if enhanced := a.enhanceIndexJoinSuggestion(table, index); enhanced != "" {
					suggestion = enhanced
				}
			}

			// Build informative message showing both absolute and relative time
			timeDesc := ""
			if kvTime > 0 {
				timeDesc = fmt.Sprintf(" (%.2fs KV time", kvTime)
				if timePercentage > 0 {
					timeDesc += fmt.Sprintf(", %.1f%% of total", timePercentage)
				}
				timeDesc += ")"
			}

			results = append(results, AnalysisResult{
				Category:       "index_join",
				Message:        fmt.Sprintf("Index join on %s consuming significant time%s", table, timeDesc),
				Suggestion:     suggestion,
				KVTime:         kvTime,
				CPUTime:        cpuTime,
				ContentionTime: contentionTime,
				Details: map[string]interface{}{
					"table":           table,
					"index_used":      index,
					"rows_processed":  rows,
					"time_percentage": timePercentage,
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
	totalTime := planTree.GetTotalExecutionTime()

	// Find all sort nodes
	sorts := planTree.Root.FindNodes(func(n *PlanNode) bool {
		return n.Operator == "sort"
	})

	for _, sort := range sorts {
		rows := sort.GetRowCount()
		kvTime := sort.GetKVTime()
		cpuTime := sort.GetCPUTime()
		contentionTime := sort.GetContentionTime()

		// Calculate time percentage (use CPU time for sorts as they're CPU-bound)
		var timePercentage float64
		relevantTime := cpuTime
		if relevantTime == 0 {
			relevantTime = kvTime
		}
		if totalTime > 0 && relevantTime > 0 {
			timePercentage = (relevantTime / totalTime) * 100
		}

		// Flag sorts that are expensive (high row count OR significant time)
		if rows > 10000 || timePercentage > 5.0 || relevantTime > 0.5 {
			message := fmt.Sprintf("Sort operation on ~%s rows", formatNumber(rows))

			if relevantTime > 0 {
				if cpuTime > 0 {
					message += fmt.Sprintf(" (%.2fs CPU time", cpuTime)
				} else {
					message += fmt.Sprintf(" (%.2fs", relevantTime)
				}
				if timePercentage > 0 {
					message += fmt.Sprintf(", %.1f%% of total", timePercentage)
				}
				message += ")"
			}

			results = append(results, AnalysisResult{
				Category:       "sort",
				Message:        message,
				Suggestion:     "Sorting large result sets is CPU-intensive. Consider adding an index on the ORDER BY columns to avoid the sort operation, or use LIMIT to reduce rows sorted.",
				KVTime:         kvTime,
				CPUTime:        cpuTime,
				ContentionTime: contentionTime,
				Details: map[string]interface{}{
					"estimated_rows":  rows,
					"time_percentage": timePercentage,
				},
			})
		}
	}

	return results
}

// checkRowProcessingEfficiency detects when many rows are processed low in the plan
// but filtered significantly higher up, indicating missed index opportunities
func (a *Analyzer) checkRowProcessingEfficiency(planTree *PlanTree) []AnalysisResult {
	var results []AnalysisResult
	totalTime := planTree.GetTotalExecutionTime()

	// Walk the tree looking for nodes with significant row reduction
	_ = planTree.Root.Walk(func(node *PlanNode) error {
		outputRows := node.GetRowCount()
		if outputRows == 0 || outputRows > 100000 {
			// Skip nodes with no data or already very large output
			return nil
		}

		// Calculate total rows processed by all children (inputs)
		var totalInputRows int
		for _, child := range node.Children {
			childRows := child.GetRowCount()
			totalInputRows += childRows
		}

		if totalInputRows == 0 {
			return nil
		}

		// Calculate reduction factor
		reductionFactor := float64(totalInputRows) / float64(outputRows)

		// Look for significant reductions (>10x) at filter or join nodes
		// This suggests we're processing many rows that get filtered out
		op := strings.ToLower(node.Operator)
		isSelectiveOp := strings.Contains(op, "filter") ||
			strings.Contains(op, "join") ||
			strings.Contains(op, "select")

		if isSelectiveOp && reductionFactor > 10.0 && totalInputRows > 10000 {
			kvTime := node.GetKVTime()
			cpuTime := node.GetCPUTime()

			var timePercentage float64
			if totalTime > 0 && (kvTime > 0 || cpuTime > 0) {
				relevantTime := kvTime
				if cpuTime > kvTime {
					relevantTime = cpuTime
				}
				timePercentage = (relevantTime / totalTime) * 100
			}

			// Only report if this is taking significant time
			if timePercentage > 5.0 || kvTime > 0.5 || cpuTime > 0.5 {
				message := fmt.Sprintf("Inefficient row processing: %s rows input → %s rows output (%.1fx reduction)",
					formatNumber(totalInputRows), formatNumber(outputRows), reductionFactor)

				if kvTime > 0 || cpuTime > 0 {
					message += " ("
					if kvTime > 0 {
						message += fmt.Sprintf("%.2fs KV", kvTime)
					}
					if cpuTime > 0 {
						if kvTime > 0 {
							message += ", "
						}
						message += fmt.Sprintf("%.2fs CPU", cpuTime)
					}
					if timePercentage > 0 {
						message += fmt.Sprintf(", %.1f%% of total", timePercentage)
					}
					message += ")"
				}

				suggestion := fmt.Sprintf("Large reduction at %s indicates many unnecessary rows processed. ", node.Operator)

				if strings.Contains(op, "filter") {
					suggestion += "Consider creating indexes on filtered columns to push filtering down to scan level, or use more selective scans/lookup joins."
				} else if strings.Contains(op, "join") {
					suggestion += "Consider reordering joins to process fewer rows, or creating indexes to enable lookup joins instead of hash/merge joins."
				} else {
					suggestion += "Consider creating indexes or restructuring the query to reduce rows processed earlier in the plan."
				}

				results = append(results, AnalysisResult{
					Category:   "inefficient_processing",
					Message:    message,
					Suggestion: suggestion,
					KVTime:     kvTime,
					CPUTime:    cpuTime,
					Details: map[string]interface{}{
						"operator":         node.Operator,
						"input_rows":       totalInputRows,
						"output_rows":      outputRows,
						"reduction_factor": reductionFactor,
						"time_percentage":  timePercentage,
					},
				})
			}
		}

		return nil
	})

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
