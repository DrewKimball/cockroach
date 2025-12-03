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

		// Get context around the scan to extract more information
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

		// Extract performance metrics from the context
		kvTimeRegex := regexp.MustCompile(`(?i)KV time:\s*(.+?)(?:\n|│|$)`)
		cpuTimeRegex := regexp.MustCompile(`(?i)CPU time:\s*(.+?)(?:\n|│|$)`)
		contentionTimeRegex := regexp.MustCompile(`(?i)contention time:\s*(.+?)(?:\n|│|$)`)

		kvTime := 0.0
		cpuTime := 0.0
		contentionTime := 0.0

		if kvMatch := kvTimeRegex.FindStringSubmatch(context); kvMatch != nil {
			kvTime = parseTimeString(kvMatch[1])
		}
		if cpuMatch := cpuTimeRegex.FindStringSubmatch(context); cpuMatch != nil {
			cpuTime = parseTimeString(cpuMatch[1])
		}
		if contentionMatch := contentionTimeRegex.FindStringSubmatch(context); contentionMatch != nil {
			contentionTime = parseTimeString(contentionMatch[1])
		}

		// Check for spans indicating a constrained scan vs full scan
		// Look for "spans: FULL SCAN" or similar indicators
		isFullScan := strings.Contains(strings.ToLower(context), "full scan") ||
			strings.Contains(strings.ToLower(context), "spans: all")

		// Only flag scans with high row counts
		// Note: A scan of any index (primary or secondary) can be either full or constrained
		if rows > 1000 {
			severity := "warning"
			message := fmt.Sprintf("Large scan on %s@%s (~%s rows)", table, index, formatNumber(rows))

			if rows > 100000 {
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
func (a *Analyzer) checkJoins(planContent string) []AnalysisResult {
	var results []AnalysisResult

	// Look for cross joins (Cartesian products)
	// These are almost always unintentional and produce excessive rows
	crossJoinRegex := regexp.MustCompile(`(?i)\bcross\s+join\b`)
	if crossJoinRegex.MatchString(planContent) {
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

		// Extract performance metrics
		kvTimeRegex := regexp.MustCompile(`(?i)KV time:\s*(.+?)(?:\n|│|$)`)
		cpuTimeRegex := regexp.MustCompile(`(?i)CPU time:\s*(.+?)(?:\n|│|$)`)
		contentionTimeRegex := regexp.MustCompile(`(?i)contention time:\s*(.+?)(?:\n|│|$)`)

		kvTimeMatch := kvTimeRegex.FindStringSubmatch(context)
		cpuTimeMatch := cpuTimeRegex.FindStringSubmatch(context)
		contentionTimeMatch := contentionTimeRegex.FindStringSubmatch(context)

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

		kvTime := 0.0
		cpuTime := 0.0
		contentionTime := 0.0

		if kvTimeMatch != nil {
			kvTime = parseTimeString(kvTimeMatch[1])
		}
		if cpuTimeMatch != nil {
			cpuTime = parseTimeString(cpuTimeMatch[1])
		}
		if contentionTimeMatch != nil {
			contentionTime = parseTimeString(contentionTimeMatch[1])
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

		// Check if this is expensive based on absolute KV time or row count
		// Note: We'll compare to total execution time later at the reporting level
		isExpensive := (kvTime > 1.0) || (rows > 10000)

		if isExpensive {
			suggestion := "Consider adding filtered columns to the index to avoid the index join"

			// Try to enhance suggestion with schema analysis
			if suggestion = a.enhanceIndexJoinSuggestion(tableName, indexName); suggestion == "" {
				suggestion = "Consider adding filtered columns to the index to avoid the index join"
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
				Message:        fmt.Sprintf("Expensive index join on %s%s", tableName, timeDesc),
				Suggestion:     suggestion,
				KVTime:         kvTime,
				CPUTime:        cpuTime,
				ContentionTime: contentionTime,
				Details: map[string]interface{}{
					"table":          tableName,
					"index_used":     indexName,
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
func (a *Analyzer) checkSorts(planContent string) []AnalysisResult {
	var results []AnalysisResult

	// Look for actual sort operators (not just the word "sort" appearing anywhere)
	// Match "sort" as a distinct operator name, typically appearing at start of line or after whitespace
	sortRegex := regexp.MustCompile(`(?i)(?:^|\s)(sort)(?:\s|$)`)
	matches := sortRegex.FindAllStringIndex(planContent, -1)

	for _, match := range matches {
		// Get context around the sort to check row counts and metrics
		contextStart := match[0] - 100
		if contextStart < 0 {
			contextStart = 0
		}
		contextEnd := match[1] + 500
		if contextEnd > len(planContent) {
			contextEnd = len(planContent)
		}

		context := planContent[contextStart:contextEnd]

		// Look for row count
		rowRegex := regexp.MustCompile(`(\d+(?:,\d+)*)\s+rows`)
		rowMatch := rowRegex.FindStringSubmatch(context)

		rows := 0
		if rowMatch != nil {
			rowStr := strings.ReplaceAll(rowMatch[1], ",", "")
			if parsed, err := strconv.Atoi(rowStr); err == nil {
				rows = parsed
			}
		}

		// Extract performance metrics
		kvTimeRegex := regexp.MustCompile(`(?i)KV time:\s*(.+?)(?:\n|│|$)`)
		cpuTimeRegex := regexp.MustCompile(`(?i)CPU time:\s*(.+?)(?:\n|│|$)`)
		contentionTimeRegex := regexp.MustCompile(`(?i)contention time:\s*(.+?)(?:\n|│|$)`)

		kvTime := 0.0
		cpuTime := 0.0
		contentionTime := 0.0

		if kvMatch := kvTimeRegex.FindStringSubmatch(context); kvMatch != nil {
			kvTime = parseTimeString(kvMatch[1])
		}
		if cpuMatch := cpuTimeRegex.FindStringSubmatch(context); cpuMatch != nil {
			cpuTime = parseTimeString(cpuMatch[1])
		}
		if contentionMatch := contentionTimeRegex.FindStringSubmatch(context); contentionMatch != nil {
			contentionTime = parseTimeString(contentionMatch[1])
		}

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
