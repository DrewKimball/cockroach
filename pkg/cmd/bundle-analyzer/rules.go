package main

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
)

// checkTableScans detects full table scans without indexes
func (a *Analyzer) checkTableScans(planContent string) []AnalysisResult {
	var results []AnalysisResult

	// Look for "scan" operations
	scanRegex := regexp.MustCompile(`(?i)scan\s+(\w+)@(\w+)`)
	matches := scanRegex.FindAllStringSubmatch(planContent, -1)

	for _, match := range matches {
		if len(match) < 3 {
			continue
		}

		table := match[1]
		index := match[2]

		// Check if this is a primary index scan (likely full table scan)
		if strings.ToLower(index) == "primary" || strings.ToLower(index) == strings.ToLower(table) {
			// Look for row count estimates nearby
			contextStart := strings.LastIndex(planContent[:strings.Index(planContent, match[0])], "\n")
			if contextStart == -1 {
				contextStart = 0
			}
			contextEnd := strings.Index(planContent[strings.Index(planContent, match[0]):], "\n\n")
			if contextEnd == -1 {
				contextEnd = len(planContent)
			} else {
				contextEnd += strings.Index(planContent, match[0])
			}

			context := planContent[contextStart:contextEnd]

			// Look for row count in various formats
			rowRegex := regexp.MustCompile(`(\d+(?:,\d+)*)\s+rows`)
			rowMatch := rowRegex.FindStringSubmatch(context)

			rows := 0
			if rowMatch != nil {
				rowStr := strings.ReplaceAll(rowMatch[1], ",", "")
				if parsed, err := strconv.Atoi(rowStr); err == nil {
					rows = parsed
				}
			}

			if rows > 1000 {
				severity := "warning"
				if rows > 100000 {
					severity = "critical"
				}

				results = append(results, AnalysisResult{
					Severity:   severity,
					Category:   "scan",
					Message:    fmt.Sprintf("Full table scan on %s (~%s rows)", table, formatNumber(rows)),
					Suggestion: fmt.Sprintf("Consider adding an index on %s to support the query filters. Use CREATE INDEX to add appropriate indexes on filtered columns.", table),
					Details: map[string]interface{}{
						"table":          table,
						"index":          index,
						"estimated_rows": rows,
					},
				})
			}
		}
	}

	return results
}

// checkJoins detects inefficient join operations
func (a *Analyzer) checkJoins(planContent string) []AnalysisResult {
	var results []AnalysisResult

	// Look for hash joins
	if strings.Contains(strings.ToLower(planContent), "hash join") {
		results = append(results, AnalysisResult{
			Severity:   "warning",
			Category:   "join",
			Message:    "Hash join detected",
			Suggestion: "Hash joins can be expensive for large datasets. Consider if the join columns are indexed, which would allow merge joins instead.",
			Details: map[string]interface{}{
				"join_type": "hash",
			},
		})
	}

	// Look for cross joins
	if strings.Contains(strings.ToLower(planContent), "cross join") {
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

	return results
}

// checkIndexJoins detects expensive index joins
func (a *Analyzer) checkIndexJoins(planContent string) []AnalysisResult {
	var results []AnalysisResult

	// Look for index join operations
	indexJoinRegex := regexp.MustCompile(`(?i)index join.*?(\(streamer\))?`)
	matches := indexJoinRegex.FindAllStringIndex(planContent, -1)

	for _, match := range matches {
		// Get context around the index join
		contextStart := match[0] - 300
		if contextStart < 0 {
			contextStart = 0
		}
		contextEnd := match[1] + 1000
		if contextEnd > len(planContent) {
			contextEnd = len(planContent)
		}

		context := planContent[contextStart:contextEnd]

		// Extract execution time and KV time
		executionTimeRegex := regexp.MustCompile(`execution time:\s*(.+?)(?:\n|$)`)
		kvTimeRegex := regexp.MustCompile(`KV time:\s*(.+?)(?:\n|│|$)`)

		executionTimeMatch := executionTimeRegex.FindStringSubmatch(planContent)
		kvTimeMatch := kvTimeRegex.FindStringSubmatch(context)

		// Extract row counts
		postContext := context[strings.Index(strings.ToLower(context), "index join"):]
		rowCountRegex := regexp.MustCompile(`actual row count:\s*(\d+(?:,\d+)*)`)
		rowCountMatch := rowCountRegex.FindStringSubmatch(postContext)

		rows := 0
		if rowCountMatch != nil {
			rowStr := strings.ReplaceAll(rowCountMatch[1], ",", "")
			if parsed, err := strconv.Atoi(rowStr); err == nil {
				rows = parsed
			}
		}

		totalTime := 0.0
		kvTime := 0.0

		if executionTimeMatch != nil {
			totalTime = parseTimeString(executionTimeMatch[1])
		}

		if kvTimeMatch != nil {
			kvTime = parseTimeString(kvTimeMatch[1])
		}

		// Extract table information
		tableRegex := regexp.MustCompile(`table:\s*(\w+)@(\w+)`)
		tableMatch := tableRegex.FindStringSubmatch(context)

		tableName := ""
		indexName := ""

		if tableMatch != nil && len(tableMatch) >= 3 {
			tableName = tableMatch[1]
			indexName = tableMatch[2]
		}

		// Check if this is expensive
		kvFraction := 0.0
		if totalTime > 0 {
			kvFraction = kvTime / totalTime
		}

		isExpensive := (kvFraction > 0.5) || (kvFraction > 0.2 && rows > 10000) || (kvTime > 5 && totalTime < 10)

		if isExpensive {
			suggestion := "Consider adding filtered columns to the index to avoid the index join"

			// Try to enhance suggestion with schema analysis
			if suggestion = a.enhanceIndexJoinSuggestion(tableName, indexName); suggestion == "" {
				suggestion = "Consider adding filtered columns to the index to avoid the index join"
			}

			severity := "warning"
			if kvFraction > 0.8 || rows > 50000 {
				severity = "critical"
			}

			timeDesc := ""
			if totalTime > 0 {
				if totalTime >= 60 {
					timeDesc = fmt.Sprintf(" (%.1fm execution time, %.1f%% in KV)", totalTime/60, kvFraction*100)
				} else {
					timeDesc = fmt.Sprintf(" (%.1fs execution time, %.1f%% in KV)", totalTime, kvFraction*100)
				}
			}

			results = append(results, AnalysisResult{
				Severity:   severity,
				Category:   "index_join",
				Message:    fmt.Sprintf("Expensive index join on %s%s", tableName, timeDesc),
				Suggestion: suggestion,
				Details: map[string]interface{}{
					"table":            tableName,
					"index_used":       indexName,
					"execution_time":   totalTime,
					"kv_time":          kvTime,
					"kv_time_fraction": kvFraction,
					"rows_processed":   rows,
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
func (a *Analyzer) checkSorts(planContent string) []AnalysisResult {
	var results []AnalysisResult

	sortRegex := regexp.MustCompile(`(?i)sort`)
	if sortRegex.MatchString(planContent) {
		results = append(results, AnalysisResult{
			Severity:   "warning",
			Category:   "sort",
			Message:    "External sort operation detected",
			Suggestion: "Sorting can be expensive. Consider adding an index on the ORDER BY columns to avoid the sort operation, or use LIMIT to reduce rows sorted.",
			Details:    map[string]interface{}{},
		})
	}

	return results
}

// checkNetworkOperations detects excessive network operations
func (a *Analyzer) checkNetworkOperations(planContent string) []AnalysisResult {
	var results []AnalysisResult

	distributedRegex := regexp.MustCompile(`(?i)distributed`)
	matches := distributedRegex.FindAllString(planContent, -1)
	distributedCount := len(matches)

	if distributedCount > 5 {
		results = append(results, AnalysisResult{
			Severity:   "warning",
			Category:   "network",
			Message:    fmt.Sprintf("Multiple distributed operations (%d)", distributedCount),
			Suggestion: "Consider if data locality can be improved, or if some operations can be pushed down to reduce network traffic.",
			Details: map[string]interface{}{
				"distributed_ops": distributedCount,
			},
		})
	}

	return results
}

// parseTimeString parses time strings like "1m39s", "1.5s", "30ms"
func parseTimeString(timeStr string) float64 {
	if timeStr == "" {
		return 0
	}

	timeStr = strings.TrimSpace(timeStr)
	totalSeconds := 0.0

	// Extract all number+unit pairs
	timeRegex := regexp.MustCompile(`(\d+(?:\.\d+)?)\s*([smhµ]+)`)
	matches := timeRegex.FindAllStringSubmatch(timeStr, -1)

	for _, match := range matches {
		if len(match) < 3 {
			continue
		}

		value, err := strconv.ParseFloat(match[1], 64)
		if err != nil {
			continue
		}

		unit := match[2]
		switch {
		case strings.Contains(unit, "h"):
			totalSeconds += value * 3600
		case strings.Contains(unit, "m") && !strings.Contains(unit, "s"):
			totalSeconds += value * 60
		case strings.Contains(unit, "s") && !strings.Contains(unit, "m"):
			totalSeconds += value
		case strings.Contains(unit, "ms"):
			totalSeconds += value / 1000
		case strings.Contains(unit, "µs"):
			totalSeconds += value / 1000000
		}
	}

	return totalSeconds
}

// formatNumber formats a number with commas for readability
func formatNumber(n int) string {
	str := strconv.Itoa(n)
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
