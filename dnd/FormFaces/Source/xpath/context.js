// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Contains all of the context information needed during the evaluation of an
// XPath. According to the XPath specification, this is:
//
//    1. The current node.
//    2. The context position (the index of the context node within the current
//       node-set ordered in document order if the current axis is a forward
//       axis, or in reverse document order if it's a reverse axis).
//    3. The size of the current node-set.
function XPathContext(node, position, size) {
  if (node == null) {
    assert(position == null, "position is not null");
    assert(size     == null, "size is not null");
  }
  else {
    assert(position >= 1,    position + " < 1");
    assert(position <= size, position + " > " + size);
  }
  
  this.node     = node;
  this.position = position;
  this.size     = size;
  
  // Save the starting node in currentNode for the current() function.
  this.currentNode = this.node;
};

XPathContext.prototype.functionResolvers = [];

// Creates an identical copy of this context object.
XPathContext.prototype.clone = function() {
  var context = new XPathContext(this.node, this.position, this.size);

  context.contextNode       = this.contextNode;
  context.functionResolvers = this.functionResolvers;

  return context;
};

// Look up the function with the specified name.
//
// Parameters:
//     qName: A QName.
XPathContext.prototype.lookupFunction = function(qName) {
  for (var i = this.functionResolvers.length - 1; i >= 0; --i) {
    var func = this.functionResolvers[i].lookupFunction(qName);
    
    if (func != null) {
      return func;
    }
  }
  
  return null;
};

XPathContext.prototype.toString = function() {
  return this.node.nodeName + "[" + this.position + "/" + this.size + "]";
};