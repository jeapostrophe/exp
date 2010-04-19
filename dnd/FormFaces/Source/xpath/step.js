// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new path step, which is the part between a pair of slashes in an
// XPath expression.
//
// Parameters:
//    axis:       The axis along which to select nodes.
//    nodeTest:   The node test at this step.
//    predicates: An array of predicates to apply to filter the nodes from the
//                node test.
function XPathStep(axis, nodeTest, predicates) {
  this.axis       = axis;
  this.nodeTest   = nodeTest;
  this.predicates = predicates;
};

// Filters the nodes in the specified node-set, creating a new node-set.
//
// Parameters:
//     context: The current evaluation context.
//     nodeSet: The node-set to filter.
XPathStep.prototype.filter = function(context, nodeSet) {
  nodeSet = this.axis    .filter(nodeSet);
  nodeSet = this.nodeTest.filter(context, nodeSet, this.axis);
  
  for (var i = this.predicates.length - 1; i >= 0; --i) {
    nodeSet = this.predicates[i].filter(context, nodeSet, this.axis.direction);
  }
  
  return nodeSet;
};