// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new node-set, which is a list of nodes containing no duplicate
// nodes. The node-set can be iterated over like an array:
//
//     for (var i = 0; i < nodeSet.length; ++i) {
//       ...
//     }
//
// The nodes are stored in the order in which they were added.
//
// Parameters:
//     nodes: Optionally, an array or other iterable collection containing the
//            initial nodes of the node-set.
function NodeSet(nodes) {
  this.length = 0;
  
  if (typeof(nodes) != "undefined") {
    this.addAll(nodes);
  }
};

// Adds a node to the node-set, unless it is already in the node-set.
NodeSet.prototype.add = function(node) {
  if (node == null) {
    return;
  }
  
  if (!this.contains(node)) {
    this[this.length++] = node;
  }
};

// Adds an array or other iterable collection of nodes to the node-set.
NodeSet.prototype.addAll = function(nodes) {
  assert(nodes && typeof(nodes.length) != "undefined", "addAll: nodes is not a node list");
  
  for (var i = nodes.length - 1; i >= 0; --i) {
    this.add(nodes[i]);
  }
  
  return this;
};

// Adds a node to the node-set. The node must not already be in the node-set.
//
// If you can guarantee that the node is not already in the node-set, then
// addUnique will be much more efficient than add: O(1) versus O(n), where n is
// the number of elements in the node-set.
NodeSet.prototype.addUnique = function(node) {
  if (node != null) {
    this[this.length++] = node;
  }
};

// Adds an array or other iterable collection of nodes to the node-set. The two
// sets of nodes must be mutually exclusive, and the node-set being added must
// not contain any duplicate nodes.
//
// If you can guarantee that these conditions, then addAllUnique will be much
// more efficient than addAll: O(k) versus O(kn + k^2), where k is the number of
// nodes being added and n is the size of the original node-set.
NodeSet.prototype.addAllUnique = function(nodes) {
  assert(nodes && typeof(nodes.length) != "undefined", "addAllUnique: nodes is not a node list");
  
  for (var i = nodes.length - 1; i >= 0; --i) {
    this.addUnique(nodes[i]);
  }
  
  return this;
};

// Returns true if the specified node is in the node-set; otherwise, false.
NodeSet.prototype.contains = function(node) {
  // If the node is a namespace node, then we must perform a thorough equality
  // test. Namespace nodes don't exist in the DOM tree; instead, they are virtual
  // nodes created on-the-fly when the namespace axis is used, and so it is
  // possible for duplicate namespace nodes to be created. (For example, when
  // evaluating the XPath "//namespace::*".)
  if (node.nodeType == 2 && node.nodeName.match(/^xmlns(:|$)/)) {
    for (var i = this.length - 1; i >= 0; --i ) {
      if (this[i] == node) {
        return true;
      }
      
      // Check for identical prefixes and namespace URIs.
      if (this[i].nodeType == 2 && this[i].nodeName == node.nodeName && this[i].value == node.value) {
        return true;
      }
    }
  }
  // For all other node types, a simple == suffices.
  else {
    for (var i = this.length - 1; i >= 0; --i) {
      if (this[i] == node) {
        return true;
      }
    }
  }
  
  return false;
};

// Reverses the nodes in the node-set in place, altering the original node-set.
//
// Return value:
//     The node-set.
NodeSet.prototype.reverse = function() {
  for (var i = 0; i < this.length / 2; ++i) {
    var front = i;
    var back  = this.length - 1 - i;
    
    var temp    = this[front];
    this[front] = this[back];
    this[back]  = temp;
  }
  
  return this;
};

NodeSet.prototype.toString = function() {
  var string = "";
  
  for (var i = 0; i < this.length; ++i) {
    var node = this[i];
    
    if (i > 0) {
      string += ", ";
    }
    
    // Attribute node.
    if (node.nodeType == 2) {
      string += "@";
    }
    
    string += node.nodeName;
    
    // If the node contains only text nodes as children, display its value.
    var simpleNode = true;
    
    for (var child = node.firstChild; child != null; child = child.nextSibling) {
      if (!isTextNode(child)) {
        simpleNode = false;
        break;
      }
    }
    
    if (simpleNode) {
      string += "=" + XPathFunction.stringValueOf(node);
    }
  }
  
  return "{" + string + "}";
};