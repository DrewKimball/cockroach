package main

import (
	"fmt"
	"strings"

	"github.com/cockroachdb/cockroach/pkg/util/humanizeutil"
)

// OpMatcher is a function that returns true if a node matches the rule's
// criteria.
type OpMatcher func(node *PlanNode) bool

// RulePre is executed during pre-order traversal before visiting children.
// It can modify NodeInfo metadata and return false to skip visiting children.
type RulePre func(info *NodeInfo, state RuleState) bool

// RulePost is executed during post-order traversal after visiting children.
// It can inspect child info and append issues to the state.
type RulePost func(info *NodeInfo, state RuleState)

// RuleState provides access to shared state across rule executions.
type RuleState interface {
	// AddIssue appends an issue to the results.
	AddIssue(issue AnalysisResult)

	// GetState retrieves state stored by this rule.
	GetState(key string) interface{}

	// SetState stores state for this rule to use later.
	SetState(key string, value interface{})
}

// Rule represents a single analysis rule that can match operators and
// execute logic during tree traversal.
type Rule struct {
	// Name is a human-readable identifier for this rule.
	Name string

	// Matcher determines if this rule should execute for a given node.
	Matcher OpMatcher

	// Pre is called during pre-order traversal (optional).
	Pre RulePre

	// Post is called during post-order traversal (optional).
	Post RulePost
}

// RuleBasedVisitor is a single visitor that executes registered rules.
type RuleBasedVisitor struct {
	rules  []Rule
	issues []AnalysisResult
	state  map[string]interface{}
}

// NewRuleBasedVisitor creates a visitor with the given rules.
func NewRuleBasedVisitor(rules []Rule) *RuleBasedVisitor {
	return &RuleBasedVisitor{
		rules:  rules,
		issues: make([]AnalysisResult, 0),
		state:  make(map[string]interface{}),
	}
}

func (v *RuleBasedVisitor) AddIssue(issue AnalysisResult) {
	v.issues = append(v.issues, issue)
}

func (v *RuleBasedVisitor) GetState(key string) interface{} {
	return v.state[key]
}

func (v *RuleBasedVisitor) SetState(key string, value interface{}) {
	v.state[key] = value
}

func (v *RuleBasedVisitor) Issues() []AnalysisResult {
	return v.issues
}

func (v *RuleBasedVisitor) VisitPre(info *NodeInfo) bool {
	// Execute all matching rules' Pre functions.
	for _, rule := range v.rules {
		if rule.Matcher != nil && !rule.Matcher(info.Node) {
			continue
		}
		if rule.Pre != nil {
			if !rule.Pre(info, v) {
				return false
			}
		}
	}
	return true
}

func (v *RuleBasedVisitor) VisitPost(info *NodeInfo) {
	// Execute all matching rules' Post functions.
	for _, rule := range v.rules {
		if rule.Matcher != nil && !rule.Matcher(info.Node) {
			continue
		}
		if rule.Post != nil {
			rule.Post(info, v)
		}
	}
}

// Standard matchers.

func matchesOp(opName string) OpMatcher {
	return func(node *PlanNode) bool {
		return strings.Contains(strings.ToLower(node.Operator), strings.ToLower(opName))
	}
}

func exactOp(opName string) OpMatcher {
	return func(node *PlanNode) bool {
		return strings.ToLower(node.Operator) == strings.ToLower(opName)
	}
}

// GetDefaultRules returns the standard set of analysis rules.
func GetDefaultRules() []Rule {
	return []Rule{
		filterRule(),
		nonFilterRule(),
		indexJoinRule(),
		scanRule(),
		crossJoinRule(),
		joinBlowupRule(),
		sortRule(),
	}
}

// filterRule detects filters and propagates column information to descendants.
func filterRule() Rule {
	return Rule{
		Name:    "filter",
		Matcher: matchesOp("filter"),
		Pre: func(info *NodeInfo, state RuleState) bool {
			node := info.Node

			// Get the filter predicate.
			filterPred := node.GetAttribute("filter")
			if filterPred == "" {
				filterPred = node.GetAttribute("pred")
			}

			// Extract column names from filter predicate.
			filterCols := extractColumnNames(filterPred)
			if len(filterCols) > 0 {
				// Get existing filter map from state.
				var filterMap map[*PlanNode][]string
				if existing := state.GetState("filter_columns"); existing != nil {
					filterMap = existing.(map[*PlanNode][]string)
				} else {
					filterMap = make(map[*PlanNode][]string)
					state.SetState("filter_columns", filterMap)
				}

				// Propagate filter columns to all descendants.
				for _, child := range node.Children {
					propagateFilterColumnsDown(child, filterCols, filterMap)
				}
			}

			// Store any parent filter columns in this node's metadata too.
			if filterMap, ok := state.GetState("filter_columns").(map[*PlanNode][]string); ok {
				if cols, ok := filterMap[node]; ok {
					info.SetMetadata("parent_filter_columns", cols)
				}
			}

			return true
		},
		Post: func(info *NodeInfo, state RuleState) {
			node := info.Node

			// Calculate selectivity.
			outputRows := node.GetRowCount()
			var inputRows int
			if len(info.ChildInfo) > 0 {
				inputRows = info.ChildInfo[0].Node.GetRowCount()
			}

			// Store selectivity for parent nodes.
			if inputRows > 0 {
				selectivity := float64(outputRows) / float64(inputRows)
				info.SetMetadata("selectivity", selectivity)
				info.SetMetadata("reduction_factor", float64(inputRows)/float64(outputRows))
			}

			// Check if this filter is highly selective on large input.
			if inputRows > 10000 && outputRows > 0 {
				reductionFactor := float64(inputRows) / float64(outputRows)
				if reductionFactor > 10.0 {
					kvTime := node.GetKVTime()
					cpuTime := node.GetCPUTime()

					var timePercentage float64
					relevantTime := kvTime
					if cpuTime > kvTime {
						relevantTime = cpuTime
					}
					if info.TotalTime > 0 && relevantTime > 0 {
						timePercentage = (relevantTime / info.TotalTime) * 100
					}

					// Only report if taking significant time.
					if timePercentage > 5.0 || kvTime > 0.5 || cpuTime > 0.5 {
						suggestion := "Highly selective filter processing many rows. Consider pushing filter down to scan by creating an index on filtered columns, or converting to a lookup join."

						state.AddIssue(AnalysisResult{
							Category:   "inefficient_processing",
							Message:    fmt.Sprintf("Selective filter: %s rows input → %s rows output (%.1fx reduction)", humanizeutil.Count(uint64(inputRows)), humanizeutil.Count(uint64(outputRows)), reductionFactor),
							Suggestion: suggestion,
							KVTime:     kvTime,
							CPUTime:    cpuTime,
							Details: map[string]interface{}{
								"operator":         node.Operator,
								"input_rows":       inputRows,
								"output_rows":      outputRows,
								"reduction_factor": reductionFactor,
								"time_percentage":  timePercentage,
							},
						})
					}
				}
			}
		},
	}
}

// nonFilterRule propagates filter metadata to non-filter nodes.
func nonFilterRule() Rule {
	return Rule{
		Name: "non-filter",
		Matcher: func(node *PlanNode) bool {
			return !strings.Contains(strings.ToLower(node.Operator), "filter")
		},
		Pre: func(info *NodeInfo, state RuleState) bool {
			// Store any parent filter columns in this node's metadata.
			if filterMap, ok := state.GetState("filter_columns").(map[*PlanNode][]string); ok {
				if cols, ok := filterMap[info.Node]; ok {
					info.SetMetadata("parent_filter_columns", cols)
				}
			}
			return true
		},
	}
}

// indexJoinRule detects expensive index joins and suggests covering indexes.
func indexJoinRule() Rule {
	return Rule{
		Name:    "index_join",
		Matcher: matchesOp("index join"),
		Post: func(info *NodeInfo, state RuleState) {
			node := info.Node
			table, index := node.GetTableAndIndex()
			rows := node.GetRowCount()
			kvTime := node.GetKVTime()
			cpuTime := node.GetCPUTime()
			contentionTime := node.GetContentionTime()

			// Calculate percentage of total time spent in this index join.
			var timePercentage float64
			if info.TotalTime > 0 && kvTime > 0 {
				timePercentage = (kvTime / info.TotalTime) * 100
			}

			// Flag if it takes >10% of total time OR has high absolute
			// time/rows. This surfaces index joins that are a significant
			// fraction of execution.
			isExpensive := (timePercentage > 10.0) || (kvTime > 1.0) || (rows > 10000)

			if !isExpensive {
				return
			}

			// Check if this node has filter metadata from parent.
			suggestion := "Consider creating a covering index that includes the retrieved columns to eliminate the index join."

			if filterCols, ok := info.GetMetadata("parent_filter_columns").([]string); ok && len(filterCols) > 0 {
				// Parent has a filter - suggest adding those columns.
				suggestion = fmt.Sprintf(
					"Index join has selective filter on parent. Consider adding filtered columns (%s) to index %s as key or STORING columns. Example: CREATE INDEX %s_covering ON %s (..., %s) STORING (...)",
					strings.Join(filterCols, ", "),
					index,
					index,
					table,
					strings.Join(filterCols, ", "),
				)
			}

			// Build informative message showing both absolute and relative
			// time.
			timeDesc := ""
			if kvTime > 0 {
				timeDesc = fmt.Sprintf(" (%.2fs KV time", kvTime)
				if timePercentage > 0 {
					timeDesc += fmt.Sprintf(", %.1f%% of total", timePercentage)
				}
				timeDesc += ")"
			}

			state.AddIssue(AnalysisResult{
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
		},
	}
}

// scanRule detects large scans and checks for parent filters.
func scanRule() Rule {
	return Rule{
		Name:    "scan",
		Matcher: exactOp("scan"),
		Post: func(info *NodeInfo, state RuleState) {
			node := info.Node
			table, index := node.GetTableAndIndex()
			if table == "" {
				return
			}

			rows := node.GetRowCount()
			isFullScan := node.IsFullScan()
			kvTime := node.GetKVTime()
			cpuTime := node.GetCPUTime()
			contentionTime := node.GetContentionTime()

			// Calculate percentage of total time.
			var timePercentage float64
			if info.TotalTime > 0 && kvTime > 0 {
				timePercentage = (kvTime / info.TotalTime) * 100
			}

			// Only flag scans with high row counts or significant time.
			if rows <= 1000 && kvTime <= 1.0 && timePercentage <= 10.0 {
				return
			}

			// Check if there are parent filters.
			filterCols, hasParentFilter := info.GetMetadata("parent_filter_columns").([]string)

			message := fmt.Sprintf("Large scan on %s@%s (~%s rows)", table, index, humanizeutil.Count(uint64(rows)))
			suggestion := "Consider adding an index to support the query filters, or add constraints to limit the scan."

			// Provide more specific messaging based on analysis.
			if isFullScan {
				message = fmt.Sprintf("Full scan on %s@%s (~%s rows)", table, index, humanizeutil.Count(uint64(rows)))
				suggestion = "Full scan detected. Consider adding WHERE clause constraints or an index that matches query filters."
			}

			if hasParentFilter && len(filterCols) > 0 {
				message += " with selective filter on parent"
				suggestion = fmt.Sprintf(
					"Scan has selective filter applied afterward on columns: %s. Consider creating an index on these columns to push filtering down to the scan. Example: CREATE INDEX ON %s (%s)",
					strings.Join(filterCols, ", "),
					table,
					strings.Join(filterCols, ", "),
				)
			}

			// Add time information.
			if kvTime > 0 {
				message += fmt.Sprintf(" (%.2fs KV time", kvTime)
				if timePercentage > 0 {
					message += fmt.Sprintf(", %.1f%% of total", timePercentage)
				}
				message += ")"
			}

			state.AddIssue(AnalysisResult{
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
					"parent_filter":    hasParentFilter,
					"time_percentage":  timePercentage,
				},
			})
		},
	}
}

// crossJoinRule detects cross joins (Cartesian products).
func crossJoinRule() Rule {
	return Rule{
		Name:    "cross_join",
		Matcher: matchesOp("cross join"),
		Post: func(info *NodeInfo, state RuleState) {
			state.AddIssue(AnalysisResult{
				Category:   "join",
				Message:    "Cross join detected (Cartesian product)",
				Suggestion: "Cross joins create Cartesian products and are usually unintentional. Add appropriate JOIN conditions or WHERE clauses.",
				Details: map[string]interface{}{
					"join_type": "cross",
				},
			})
		},
	}
}

// joinBlowupRule detects joins with cardinality blowup.
func joinBlowupRule() Rule {
	return Rule{
		Name: "join_blowup",
		Matcher: func(node *PlanNode) bool {
			op := strings.ToLower(node.Operator)
			// Match hash/merge/lookup joins but not index joins.
			return (strings.Contains(op, "hash join") ||
				strings.Contains(op, "merge join") ||
				strings.Contains(op, "lookup join")) &&
				!strings.Contains(op, "index join")
		},
		Post: func(info *NodeInfo, state RuleState) {
			node := info.Node

			// Check for cardinality blowup: output rows >> input rows.
			outputRows := node.GetRowCount()
			if outputRows == 0 {
				return
			}

			// Get maximum input row count from children.
			var maxInputRows int
			for _, childInfo := range info.ChildInfo {
				childRows := childInfo.Node.GetRowCount()
				if childRows > maxInputRows {
					maxInputRows = childRows
				}
			}

			if maxInputRows == 0 {
				return
			}

			// Calculate blowup factor.
			blowupFactor := float64(outputRows) / float64(maxInputRows)

			// Flag if output is significantly larger than largest input
			// (>5x). This suggests poor join ordering or missing filters.
			if blowupFactor <= 5.0 || outputRows <= 10000 {
				return
			}

			kvTime := node.GetKVTime()
			cpuTime := node.GetCPUTime()

			var timePercentage float64
			if info.TotalTime > 0 && kvTime > 0 {
				timePercentage = (kvTime / info.TotalTime) * 100
			}

			message := fmt.Sprintf("Join producing large intermediate result: %s output rows from %s input rows (%.1fx blowup)",
				humanizeutil.Count(uint64(outputRows)), humanizeutil.Count(uint64(maxInputRows)), blowupFactor)

			if kvTime > 0 {
				message += fmt.Sprintf(" (%.2fs", kvTime)
				if timePercentage > 0 {
					message += fmt.Sprintf(", %.1f%% of total", timePercentage)
				}
				message += ")"
			}

			state.AddIssue(AnalysisResult{
				Category:   "join",
				Message:    message,
				Suggestion: "Large intermediate result from join. Consider reordering joins to reduce intermediate cardinality, or adding more selective filters earlier in the query plan.",
				KVTime:     kvTime,
				CPUTime:    cpuTime,
				Details: map[string]interface{}{
					"join_type":       node.Operator,
					"output_rows":     outputRows,
					"input_rows":      maxInputRows,
					"blowup_factor":   blowupFactor,
					"time_percentage": timePercentage,
				},
			})
		},
	}
}

// sortRule detects expensive sort operations.
func sortRule() Rule {
	return Rule{
		Name:    "sort",
		Matcher: exactOp("sort"),
		Post: func(info *NodeInfo, state RuleState) {
			node := info.Node
			rows := node.GetRowCount()
			kvTime := node.GetKVTime()
			cpuTime := node.GetCPUTime()
			contentionTime := node.GetContentionTime()

			// Calculate time percentage (use CPU time for sorts as they're
			// CPU-bound).
			var timePercentage float64
			relevantTime := cpuTime
			if relevantTime == 0 {
				relevantTime = kvTime
			}
			if info.TotalTime > 0 && relevantTime > 0 {
				timePercentage = (relevantTime / info.TotalTime) * 100
			}

			// Flag sorts that are expensive (high row count OR significant
			// time).
			if rows <= 10000 && timePercentage <= 5.0 && relevantTime <= 0.5 {
				return
			}

			message := fmt.Sprintf("Sort operation on ~%s rows", humanizeutil.Count(uint64(rows)))

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

			state.AddIssue(AnalysisResult{
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
		},
	}
}

// propagateFilterColumnsDown recursively records filter columns for a node
// and all its descendants.
func propagateFilterColumnsDown(node *PlanNode, cols []string, filterMap map[*PlanNode][]string) {
	if node == nil {
		return
	}

	// Merge with any existing filter columns for this node.
	existing := filterMap[node]
	filterMap[node] = mergeUnique(existing, cols)

	// Propagate to all children.
	for _, child := range node.Children {
		propagateFilterColumnsDown(child, cols, filterMap)
	}
}

// extractColumnNames extracts column names from a filter predicate using
// simple heuristics.
func extractColumnNames(pred string) []string {
	if pred == "" {
		return nil
	}

	var cols []string
	// Simple pattern: look for identifiers followed by comparison operators.
	// This won't be perfect but is better than parsing SQL.
	words := strings.FieldsFunc(pred, func(r rune) bool {
		return r == ' ' || r == '(' || r == ')' || r == ',' ||
			r == '<' || r == '>' || r == '=' || r == '!'
	})

	for _, word := range words {
		word = strings.TrimSpace(word)
		// Filter out numbers, keywords, and operators.
		if word == "" || isNumber(word) || isKeyword(word) {
			continue
		}
		// Likely a column name.
		cols = append(cols, word)
	}

	return cols
}

func isNumber(s string) bool {
	if s == "" {
		return false
	}
	for _, ch := range s {
		if ch < '0' || ch > '9' {
			if ch != '.' && ch != '-' {
				return false
			}
		}
	}
	return true
}

func isKeyword(s string) bool {
	keywords := map[string]bool{
		"and": true, "or": true, "not": true, "null": true,
		"true": true, "false": true, "is": true, "in": true,
	}
	return keywords[strings.ToLower(s)]
}

func mergeUnique(a, b []string) []string {
	seen := make(map[string]bool)
	result := make([]string, 0)

	for _, s := range a {
		if !seen[s] {
			result = append(result, s)
			seen[s] = true
		}
	}
	for _, s := range b {
		if !seen[s] {
			result = append(result, s)
			seen[s] = true
		}
	}

	return result
}
