package main

import (
	"fmt"
	"strconv"
	"strings"
)

// PlanNode represents a node in the query plan tree
type PlanNode struct {
	// Operator is the name of the operator (e.g., "scan", "index join", "filter")
	Operator string

	// Attributes contains all the attributes for this node
	Attributes map[string]string

	// Children are the child nodes
	Children []*PlanNode

	// Parent is the parent node (nil for root)
	Parent *PlanNode

	// Depth is the indentation depth of this node
	Depth int

	// RawText is the original text for this node (for debugging)
	RawText string
}

// PlanTree represents the parsed query plan
type PlanTree struct {
	// Root is the root node of the plan tree
	Root *PlanNode

	// Metadata contains top-level plan metadata (execution time, etc.)
	Metadata map[string]string

	// PostQueries contains any post-query plans (e.g., cascades)
	PostQueries []*PlanTree
}

// ParsePlanTree parses a plan.txt file into a tree structure
func ParsePlanTree(planContent string) (*PlanTree, error) {
	lines := strings.Split(planContent, "\n")

	tree := &PlanTree{
		Metadata: make(map[string]string),
	}

	// Parse metadata (lines before the first operator)
	var planStart int
	for i, line := range lines {
		trimmed := strings.TrimSpace(line)
		if trimmed == "" {
			continue
		}

		// Check if this is an operator line (starts with •)
		if strings.HasPrefix(trimmed, "•") {
			planStart = i
			break
		}

		// Parse metadata key: value
		if strings.Contains(line, ":") {
			parts := strings.SplitN(line, ":", 2)
			if len(parts) == 2 {
				key := strings.TrimSpace(parts[0])
				value := strings.TrimSpace(parts[1])
				tree.Metadata[key] = value
			}
		}
	}

	// Parse the plan tree
	if planStart < len(lines) {
		root, err := parsePlanNodes(lines[planStart:])
		if err != nil {
			return nil, err
		}
		tree.Root = root
	}

	return tree, nil
}

// parsePlanNodes recursively parses plan nodes from lines
func parsePlanNodes(lines []string) (*PlanNode, error) {
	if len(lines) == 0 {
		return nil, nil
	}

	// Find the root node (first operator)
	var rootLine string
	var rootIdx int
	for i, line := range lines {
		if strings.Contains(line, "•") {
			rootLine = line
			rootIdx = i
			break
		}
	}

	if rootLine == "" {
		return nil, nil
	}

	// Calculate depth based on indentation
	depth := calculateDepth(rootLine)

	// Extract operator name
	operator := extractOperator(rootLine)

	root := &PlanNode{
		Operator:   operator,
		Attributes: make(map[string]string),
		Depth:      depth,
		RawText:    rootLine,
	}

	// Parse attributes and children
	i := rootIdx + 1
	for i < len(lines) {
		line := lines[i]
		if line == "" || strings.TrimSpace(line) == "" {
			i++
			continue
		}

		lineDepth := calculateDepth(line)

		// Check if this is a child node (contains •)
		if strings.Contains(line, "•") {
			// This is a child operator
			childLines := lines[i:]
			child, err := parsePlanNodes(childLines)
			if err != nil {
				return nil, err
			}
			if child != nil {
				child.Parent = root
				root.Children = append(root.Children, child)

				// Skip past the child's subtree
				childEnd := findSubtreeEnd(childLines, child.Depth)
				i += childEnd
			}
			continue
		}

		// Check if this is an attribute line (contains │)
		if strings.Contains(line, "│") && strings.Contains(line, ":") {
			// Parse attribute
			key, value := parseAttribute(line)
			if key != "" {
				root.Attributes[key] = value
			}
			i++
			continue
		}

		// If we hit a line with lower depth, we're done with this node
		if lineDepth < depth {
			break
		}

		i++
	}

	return root, nil
}

// calculateDepth calculates the indentation depth of a line
func calculateDepth(line string) int {
	// Count leading spaces before the first non-space, non-box-drawing character
	depth := 0
	for _, ch := range line {
		if ch == ' ' {
			depth++
		} else if ch == '│' || ch == '└' || ch == '├' {
			// Box drawing characters don't count as depth
			continue
		} else {
			break
		}
	}
	return depth
}

// extractOperator extracts the operator name from a line
func extractOperator(line string) string {
	// Find the • character and extract the text after it
	idx := strings.Index(line, "•")
	if idx == -1 {
		return ""
	}

	// Extract everything after • until newline or comment
	rest := strings.TrimSpace(line[idx+len("•"):])
	return rest
}

// parseAttribute parses a key: value attribute line
func parseAttribute(line string) (string, string) {
	// Remove box-drawing characters
	clean := strings.ReplaceAll(line, "│", "")
	clean = strings.ReplaceAll(clean, "└", "")
	clean = strings.ReplaceAll(clean, "├", "")
	clean = strings.TrimSpace(clean)

	// Split on first colon
	parts := strings.SplitN(clean, ":", 2)
	if len(parts) != 2 {
		return "", ""
	}

	key := strings.TrimSpace(parts[0])
	value := strings.TrimSpace(parts[1])
	return key, value
}

// findSubtreeEnd finds the end of a subtree starting at the given depth
func findSubtreeEnd(lines []string, startDepth int) int {
	if len(lines) == 0 {
		return 0
	}

	// Start at 1 since lines[0] is the current node
	for i := 1; i < len(lines); i++ {
		line := lines[i]
		if strings.TrimSpace(line) == "" {
			continue
		}

		// Check if this line contains a node at the same or lower depth
		if strings.Contains(line, "•") {
			lineDepth := calculateDepth(line)
			if lineDepth <= startDepth {
				return i
			}
		}
	}

	return len(lines)
}

// GetAttribute retrieves an attribute value, or empty string if not found
func (n *PlanNode) GetAttribute(key string) string {
	return n.Attributes[key]
}

// GetAttributeFloat retrieves an attribute as a float64
func (n *PlanNode) GetAttributeFloat(key string) float64 {
	value := n.Attributes[key]
	if value == "" {
		return 0
	}

	// Try to parse as time
	if timeValue := parseTimeString(value); timeValue > 0 {
		return timeValue
	}

	// Try to parse as number (removing commas)
	value = strings.ReplaceAll(value, ",", "")
	if f, err := strconv.ParseFloat(value, 64); err == nil {
		return f
	}

	return 0
}

// GetAttributeInt retrieves an attribute as an int
func (n *PlanNode) GetAttributeInt(key string) int {
	value := n.Attributes[key]
	if value == "" {
		return 0
	}

	// Remove commas and parse
	value = strings.ReplaceAll(value, ",", "")
	if i, err := strconv.Atoi(value); err == nil {
		return i
	}

	return 0
}

// GetKVTime extracts KV time from node attributes
func (n *PlanNode) GetKVTime() float64 {
	return n.GetAttributeFloat("KV time")
}

// GetCPUTime extracts CPU time from node attributes
func (n *PlanNode) GetCPUTime() float64 {
	return n.GetAttributeFloat("sql cpu time")
}

// GetContentionTime extracts contention time from node attributes
func (n *PlanNode) GetContentionTime() float64 {
	return n.GetAttributeFloat("contention time")
}

// GetRowCount extracts actual row count from node attributes
func (n *PlanNode) GetRowCount() int {
	return n.GetAttributeInt("actual row count")
}

// GetEstimatedRowCount extracts estimated row count
func (n *PlanNode) GetEstimatedRowCount() int {
	estStr := n.GetAttribute("estimated row count")
	if estStr == "" {
		return 0
	}

	// Parse "333 (missing stats)" format
	parts := strings.Fields(estStr)
	if len(parts) > 0 {
		value := strings.ReplaceAll(parts[0], ",", "")
		if i, err := strconv.Atoi(value); err == nil {
			return i
		}
	}

	return 0
}

// IsFullScan checks if this node represents a full scan
func (n *PlanNode) IsFullScan() bool {
	spans := n.GetAttribute("spans")
	return strings.Contains(strings.ToLower(spans), "full scan") ||
		strings.Contains(strings.ToLower(spans), "all")
}

// GetTableAndIndex extracts table and index name from a scan node
func (n *PlanNode) GetTableAndIndex() (table string, index string) {
	tableAttr := n.GetAttribute("table")
	if tableAttr == "" {
		return "", ""
	}

	// Parse "table@index" format
	parts := strings.Split(tableAttr, "@")
	if len(parts) == 2 {
		return parts[0], parts[1]
	}

	return tableAttr, ""
}

// Walk performs a depth-first walk of the tree, calling fn for each node
func (n *PlanNode) Walk(fn func(*PlanNode) error) error {
	if n == nil {
		return nil
	}

	if err := fn(n); err != nil {
		return err
	}

	for _, child := range n.Children {
		if err := child.Walk(fn); err != nil {
			return err
		}
	}

	return nil
}

// FindNodes returns all nodes matching the predicate
func (n *PlanNode) FindNodes(predicate func(*PlanNode) bool) []*PlanNode {
	var result []*PlanNode

	_ = n.Walk(func(node *PlanNode) error {
		if predicate(node) {
			result = append(result, node)
		}
		return nil
	})

	return result
}

// String provides a debug representation of the node
func (n *PlanNode) String() string {
	return fmt.Sprintf("PlanNode{Operator: %s, Depth: %d, Attributes: %d, Children: %d}",
		n.Operator, n.Depth, len(n.Attributes), len(n.Children))
}

// GetTotalExecutionTime extracts total execution time from plan metadata
func (t *PlanTree) GetTotalExecutionTime() float64 {
	execTime := t.Metadata["execution time"]
	return parseTimeString(execTime)
}

// parseTimeString parses time strings like "1m39s", "1.5s", "30ms"
func parseTimeString(timeStr string) float64 {
	if timeStr == "" {
		return 0
	}

	timeStr = strings.TrimSpace(timeStr)
	totalSeconds := 0.0

	// Handle simple formats first
	if strings.HasSuffix(timeStr, "ms") {
		// Milliseconds
		value := strings.TrimSuffix(timeStr, "ms")
		if f, err := strconv.ParseFloat(value, 64); err == nil {
			return f / 1000.0
		}
	} else if strings.HasSuffix(timeStr, "µs") || strings.HasSuffix(timeStr, "us") {
		// Microseconds
		value := strings.TrimSuffix(strings.TrimSuffix(timeStr, "µs"), "us")
		if f, err := strconv.ParseFloat(value, 64); err == nil {
			return f / 1000000.0
		}
	} else if strings.HasSuffix(timeStr, "s") && !strings.Contains(timeStr, "m") {
		// Seconds (simple case)
		value := strings.TrimSuffix(timeStr, "s")
		if f, err := strconv.ParseFloat(value, 64); err == nil {
			return f
		}
	}

	// Handle compound formats like "1m39s"
	// Parse minutes
	if strings.Contains(timeStr, "m") {
		parts := strings.Split(timeStr, "m")
		if len(parts) >= 1 {
			if mins, err := strconv.ParseFloat(parts[0], 64); err == nil {
				totalSeconds += mins * 60
			}
			if len(parts) > 1 {
				// Parse remaining seconds
				remaining := strings.TrimSuffix(parts[1], "s")
				if secs, err := strconv.ParseFloat(remaining, 64); err == nil {
					totalSeconds += secs
				}
			}
		}
		return totalSeconds
	}

	// Handle hours
	if strings.Contains(timeStr, "h") {
		parts := strings.Split(timeStr, "h")
		if len(parts) >= 1 {
			if hours, err := strconv.ParseFloat(parts[0], 64); err == nil {
				totalSeconds += hours * 3600
			}
			// Recursively parse the rest
			if len(parts) > 1 {
				totalSeconds += parseTimeString(parts[1])
			}
		}
		return totalSeconds
	}

	return 0
}
