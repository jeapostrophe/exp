// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new axis.
//
// Parameters:
//     direction: The direction of the axis; either XPathAxis.Direction.FORWARD
//                or XPathAxis.Direction.REVERSE.
function XPathAxis(name, direction) {
  this.name      = name;
  this.direction = direction;
};

// Applies the axis filter to the nodes in the node-set.
//
// Parameters:
//     nodeSet: The node-set to apply the axis to.
//
// Return value:
//     A node-set containing the nodes selected by the axis.
XPathAxis.prototype.filter = function(nodeSet) {
  var result = new NodeSet();
  var setLen = nodeSet.length - 1;
  
  for (var i = setLen; i >= 0; --i) {
    // Avoid an expensive addAll() when we can.
    if(i == setLen) {
      result = this.filterNode(nodeSet[i]);
    }
    else {
      result.addAll(this.filterNode(nodeSet[i]));
    }
  }
  
  return result;
};

// Applies the axis filter to the specified node.
//
// Parameters:
//     node: The node to apply the axis filter to.
//
// Return value:
//     A node-set containing the nodes selected by the axis.
XPathAxis.prototype.filterNode = function(node) {
  assert(false, "filterNode not implemented");
};

XPathAxis.prototype.toString = function() {
  return this.name;
};

XPathAxis.Direction         = { };
XPathAxis.Direction.FORWARD = 0;
XPathAxis.Direction.REVERSE = 1;



// The child axis.
XPathAxis.CHILD = new XPathAxis("child", XPathAxis.Direction.FORWARD);

XPathAxis.CHILD.filterNode = function(node) {
  var nodeSet = new NodeSet();
  
  // Attribute nodes actually have children; don't ever return them.
  if (node.nodeType != 2) {
    nodeSet.addAllUnique(node.childNodes);
  }
  
  return nodeSet;
};



// The descendant axis.
XPathAxis.DESCENDANT = new XPathAxis("descendant", XPathAxis.Direction.FORWARD);

XPathAxis.DESCENDANT.filterNode = function(node) {
  // Attribute nodes actually have children; don't ever return them.
  if (node.nodeType == 2) {
    return new NodeSet();
  }
  
  // For speed, we'll do an iterative depth-first traversal instead of a recursive
  // one.
  var nodeSet = new NodeSet();
  var stack   = [];
  
  for (var child = node.lastChild; child != null; child = child.previousSibling) {
    stack.push(child);
  }
  
  while (stack.length > 0) {
    var parent = stack.pop();
    
    nodeSet.addUnique(parent);
    
    for (var child = parent.lastChild; child != null; child = child.previousSibling) {
      stack.push(child);
    }
  }
  
  return nodeSet;
};



// The descendant-or-self axis.
XPathAxis.DESCENDANT_OR_SELF = new XPathAxis("descendant-or-self", XPathAxis.Direction.FORWARD);

XPathAxis.DESCENDANT_OR_SELF.filterNode = function(node) {
  // Attribute nodes actually have children; don't ever return them.
  if (node.nodeType == 2) {
    return new NodeSet();
  }
  
  // For speed, we'll do an iterative depth-first traversal instead of a recursive
  // one.
  var nodeSet = new NodeSet();
  var stack   = [node];
  
  while (stack.length > 0) {
    var parent = stack.pop();
    
    nodeSet.addUnique(parent);
    
    for (var child = parent.lastChild; child != null; child = child.previousSibling) {
      stack.push(child);
    }
  }
  
  return nodeSet;
};



// The parent axis.
XPathAxis.PARENT = new XPathAxis("parent", XPathAxis.Direction.REVERSE);

XPathAxis.PARENT.filterNode = function(node) {
  if (node.nodeType == 2) {
    if (typeof(node.ownerElement) != "undefined") {
      return new NodeSet([node.ownerElement]);
    }
    else {
      // Internet Explorer, aggravatingly enough, doesn't support 
      // attribute.ownerElement, so we must instead search the entire document to find
      // the attribute's owner.
      return new NodeSet([ownerElement(node.ownerDocument, node)]);
      
      function ownerElement(node, attribute) {
        var atts = node.attributes;
        if (atts != null) {
          for (var i = atts.length - 1; i >= 0; --i) {
            if (atts.item(i) == attribute) {
              return node;
            }
          }
        }
        
        for (var child = node.firstChild; child != null; child = child.nextSibling) {
          var element = ownerElement(child, attribute);
          
          if (element != null) {
            return element;
          }
        }
        
        return null;
      };
    }
  }
  else if (node.parentNode != null && node.parentNode.nodeType != 9) {
    return new NodeSet([node.parentNode]);
  }
  else {
    return new NodeSet();
  }
};



// The ancestor axis.
XPathAxis.ANCESTOR = new XPathAxis("ancestor", XPathAxis.Direction.REVERSE);

XPathAxis.ANCESTOR.filterNode = function(node) {
  var nodeSet = new NodeSet();
  var parent  = XPathAxis.PARENT.filterNode(node);
  
  node = parent.length > 0 ? parent[0] : null;
  
  while (node != null && node.nodeType != 9) {
    nodeSet.addUnique(node);
    node = node.parentNode;
  }
  
  return nodeSet.reverse();
};



// The ancestor-or-self axis.
XPathAxis.ANCESTOR_OR_SELF = new XPathAxis("ancestor-or-self", XPathAxis.Direction.REVERSE);

XPathAxis.ANCESTOR_OR_SELF.filterNode = function(node) {
  var nodeSet = new NodeSet();
  
  nodeSet.addAllUnique(XPathAxis.ANCESTOR.filterNode(node));
  nodeSet.addUnique   (node);
  
  return nodeSet;
};



// The following-sibling axis.
XPathAxis.FOLLOWING_SIBLING = new XPathAxis("following-sibling", XPathAxis.Direction.FORWARD);

XPathAxis.FOLLOWING_SIBLING.filterNode = function(node) {
  var nodeSet = new NodeSet();
  
  while (node.nextSibling != null) {
    nodeSet.addUnique(node = node.nextSibling);
  }
  
  return nodeSet;
};



// The preceding-sibling axis.
XPathAxis.PRECEDING_SIBLING = new XPathAxis("preceding-sibling", XPathAxis.Direction.REVERSE);

XPathAxis.PRECEDING_SIBLING.filterNode = function(node) {
  if (node.parentNode == null) {
    return new NodeSet();
  }
  
  var nodeSet = new NodeSet();
  
  for (var sibling = node.previousSibling; sibling != null; sibling = sibling.previousSibling) {
    nodeSet.addUnique(sibling);
  }
  
  return nodeSet;
};



// The following axis.
XPathAxis.FOLLOWING = new XPathAxis("following", XPathAxis.Direction.FORWARD);

XPathAxis.FOLLOWING.filterNode = function(node) {
  function following(node) {
    if (node.nextSibling != null) {
      var nodeSet = new NodeSet();
      
      nodeSet.addUnique   (node.nextSibling);
      nodeSet.addAllUnique(following(node.nextSibling));
      
      return nodeSet;
    }
    else if (node.parentNode != null) {
      return following(node.parentNode);
    }
    else {
      return new NodeSet();
    }
  };
  
  return following(node);
};



// The preceding axis.
XPathAxis.PRECEDING = new XPathAxis("preceding", XPathAxis.Direction.REVERSE);

XPathAxis.PRECEDING.filterNode = function(node) {
  function preceding(node) {
    if (node.previousSibling != null) {
      return preceding(node.previousSibling)
            .addUnique(node.previousSibling);
    }
    else if (node.parentNode != null) {
      return preceding(node.parentNode);
    }
    else {
      return new NodeSet();
    }
  };
  
  return preceding(node);
};


// The attribute axis.
XPathAxis.ATTRIBUTE = new XPathAxis("attribute", XPathAxis.Direction.FORWARD);

XPathAxis.ATTRIBUTE.filterNode = function(node) {
  if (node.attributes == null) {
    return new NodeSet();
  }
  
  // Get all of the attributes that aren't namespace declarations.
  var nodeSet = new NodeSet();
  var atts    = node.attributes;
  
  for (var i = atts.length - 1; i >= 0; --i) {
    var attribute = atts.item(i);
    
    if (!attribute.name.match(/^xmlns(:|$)/)) {
      nodeSet.addUnique(attribute);
    }
  }
  
  return nodeSet;
};



// The namespace axis.
XPathAxis.NAMESPACE = new XPathAxis("namespace", XPathAxis.Direction.FORWARD);

// If true, an xmlns:xml="http://www.w3.org/XML/1998/namespace" attribute will
// always be included in the returned node-set.
XPathAxis.NAMESPACE.includeXmlNamespace = true;

XPathAxis.NAMESPACE.filterNode = function(node) {
  // Only element nodes have namespace nodes.
  if (node.nodeType != 1) {
    return new NodeSet();
  }
  
  var prefixesSeen = { };
  var nodeSet      = new NodeSet();
  
  if (this.includeXmlNamespace) {
    try {
      // The "xml" namespace is implicitly declared in every document.
      var xmlNamespaceNode       = node.ownerDocument.createAttribute("xmlns:xml");
          xmlNamespaceNode.value = "http://www.w3.org/XML/1998/namespace";
        
      nodeSet.addUnique(xmlNamespaceNode);
    }
    catch (exception) {
      // Internet Explorer won't allow the attribute to be created, so don't try
      // again.
      this.includeXmlNamespace = false;
    }
  }
  
  for (; node != null && node.nodeType == 1; node = node.parentNode) {
    var atts   = node.attributes;
    
    for (var i = atts.length - 1; i >= 0; --i) {
      var attribute = atts.item(i);
      var value     = attribute.value;
      var prefix;

      if (attribute.name.match(/^xmlns(:|$)/)) {
        var prefix = attribute.name.substring(6);
        
        // If we've seen this prefix already, skip it.
        if (typeof(prefixesSeen[prefix]) != "undefined") {
          continue;
        }
        
        prefixesSeen[prefix] = true;
        
        // The declaration xmlns="" cancels out the default namespace, and is not a
        // regular namespace declaration.
        if (!(prefix == "" && value == "")) {
          nodeSet.addUnique(attribute);
        }
      }
    }
  }
  
  return nodeSet;
};



// The self axis.
XPathAxis.SELF = new XPathAxis("self", XPathAxis.Direction.FORWARD);

// Override the default filter function with a more efficient implementation.
XPathAxis.SELF.filter = function(nodeSet) {
  return nodeSet;
};

XPathAxis.SELF.filterNode = function(node) {
  return new NodeSet([node]);
};