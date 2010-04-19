// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new location path, which is a series of steps in a path, each step
// searching for particular nodes along an axis.
XPathLocationPath = function(isAbsolute, steps) {
  this.isAbsolute = isAbsolute;
  this.steps      = steps;
};

// A location path can be evaluated as an expression.
XPathLocationPath.inherits(XPathExpression);


// Evaluates the location path starting from the nodes in the specified
// node-set, returning the set of nodes selected by the path.
//
// Parameters:
//     nodeSet: The initial node-set.
//
// Return value:
//     The node-set obtained by evaluating the location path starting at the
//     initial node-set.
XPathLocationPath.prototype.filter = function(context, nodeSet) {
  var stepLen = this.steps.length;
  for (var i = 0; i < stepLen; ++i) {
    nodeSet = this.steps[i].filter(context, nodeSet);
  }
  return nodeSet;
};

// Returns the set of nodes selected by the path starting from either the
// context node if the path is relative, or the document root if the path is
// absolute.
//
// Parameters:
//     context: The current evaluation context.
//
// Return value:
//     The nodes selected by the path.
XPathLocationPath.prototype.evaluate = function(context) {
  var contextNode;
  
  if (context.node == null) {
    contextNode = null;
  }
  else if (this.isAbsolute) {
    contextNode = (context.node.nodeType == 9)
      ? context.node
      : context.node.ownerDocument;
  }
  else {
    contextNode = context.node;
  }
    
  return this.filter(context, new NodeSet([contextNode]));
};