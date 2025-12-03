package main

// NodeInfo holds analysis information collected for a node.
// This is passed to visitor functions to provide context about the node
// and its children.
type NodeInfo struct {
	// Node is the plan node being analyzed.
	Node *PlanNode

	// ChildInfo contains the NodeInfo for each child node.
	// This is populated before VisitPost is called.
	ChildInfo []*NodeInfo

	// TotalTime is the total execution time of the query.
	TotalTime float64

	// Metadata holds arbitrary analysis data that rules can attach.
	// For example, a filter might record its selectivity here for parent
	// nodes to inspect.
	Metadata map[string]interface{}
}

// NewNodeInfo creates a new NodeInfo for a node.
func NewNodeInfo(node *PlanNode, totalTime float64) *NodeInfo {
	return &NodeInfo{
		Node:      node,
		ChildInfo: make([]*NodeInfo, 0),
		TotalTime: totalTime,
		Metadata:  make(map[string]interface{}),
	}
}

// GetMetadata retrieves metadata by key, returning nil if not found.
func (ni *NodeInfo) GetMetadata(key string) interface{} {
	return ni.Metadata[key]
}

// SetMetadata sets metadata for this node.
func (ni *NodeInfo) SetMetadata(key string, value interface{}) {
	ni.Metadata[key] = value
}

// Walk performs a traversal of the plan tree, calling VisitPre before
// visiting children and VisitPost after.
// Returns the root NodeInfo.
func Walk(root *PlanNode, totalTime float64, visitor *RuleBasedVisitor) *NodeInfo {
	return walkInternal(root, totalTime, visitor)
}

func walkInternal(node *PlanNode, totalTime float64, visitor *RuleBasedVisitor) *NodeInfo {
	if node == nil {
		return nil
	}

	info := NewNodeInfo(node, totalTime)

	// Call VisitPre on the visitor for this node.
	if !visitor.VisitPre(info) {
		// Visitor requested to skip this node's children.
		return info
	}

	// Visit all children.
	for _, child := range node.Children {
		childInfo := walkInternal(child, totalTime, visitor)
		if childInfo != nil {
			info.ChildInfo = append(info.ChildInfo, childInfo)
		}
	}

	// Call VisitPost on the visitor for this node.
	visitor.VisitPost(info)

	return info
}
