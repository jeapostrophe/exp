// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Interface for XPath node tests, which select a set of nodes from a particular
// axis during evaluation of a location path step.
function XPathNodeTest() {
};

// Filters the node-set through the node test, keeping only nodes that pass the
// node test.
//
// Parameters:
//     context: The current evaluation context.
//     nodeSet: The current node-set.
//     axis:    The current axis.
XPathNodeTest.prototype.filter = function(context, nodeSet, axis) {
  var result = new NodeSet();
  
  for (var i = nodeSet.length - 1; i >= 0; --i) {
    var node = nodeSet[i];
  
    if (this.test(context, node, axis)) {
      result.addUnique(node);
    }
  }
  
  return result;
};

// Tests the specified node.
XPathNodeTest.prototype.test = function(context, node, axis) {
};



// "*": Allows only nodes of the axis's principal type.
function XPathStarNodeTest() {
};

XPathStarNodeTest.inherits(XPathNodeTest);

XPathStarNodeTest.prototype.test = function(context, node, axis) {
  switch (axis) {
    case XPathAxis.ATTRIBUTE:
      return node.nodeType == 2;
      
    case XPathAxis.NAMESPACE:
      return node.nodeType == 2 && node.name.match(/^xmlns(:|$)/);
      
    default:
      return node.nodeType == 1;
  }
};



// "ns::*": Allows only elements belonging to a particular namespace.
function XPathNamespaceNodeTest(namespaceURI) {
  this.namespaceURI = namespaceURI;
};

XPathNamespaceNodeTest.inherits(XPathNodeTest);

XPathNamespaceNodeTest.prototype.test = function(context, node, axis) {
  if (!XPathStarNodeTest.prototype.test.call(this, context, node, axis)) {
    return false;
  }
  
  return xmlNamespaceURI(node) == this.namespaceURI;
};



// "ns:name" or "name": Allows only elements with the specified QName, which is
// a namespace URI and local name pair. The namespace URI is "" for nodes
// without a namespace.
function XPathQNameNodeTest(qName) {
  this.qName = qName;
};

XPathQNameNodeTest.inherits(XPathNodeTest);

XPathQNameNodeTest.prototype.test = function(context, node, axis) {
  return this.qName.matches(node);
};



// comment(): Allows only comment nodes.
function XPathCommentNodeTest() {
};

XPathCommentNodeTest.inherits(XPathNodeTest);

XPathCommentNodeTest.prototype.test = function(context, node, axis) {
  return node.nodeType == 8;
};



// text(): Allows only text nodes.
function XPathTextNodeTest() {
};

XPathTextNodeTest.inherits(XPathNodeTest);

XPathTextNodeTest.prototype.test = function(context, node, axis) {
  return isTextNode(node);
};

  
  
// processing-instruction(): Allows only processing instruction nodes.
function XPathProcessingInstructionNodeTest(name) {
  this.name = name;
};

XPathProcessingInstructionNodeTest.inherits(XPathNodeTest);

XPathProcessingInstructionNodeTest.prototype.test = function(context, node, axis) {
  if (node.nodeType != 7) {
    return false;
  }
  
  if (this.name != null && node.target != this.name) {
    return false;
  }
  
  return true;
};



// node(): Allows all nodes.
function XPathNodeNodeTest() {
};

XPathNodeNodeTest.inherits(XPathNodeTest);

// Override the default implementation of testing each node, since node() is
// true for every node.
XPathNodeNodeTest.prototype.filter = function(context, nodeSet, axis) {
  return nodeSet;
};