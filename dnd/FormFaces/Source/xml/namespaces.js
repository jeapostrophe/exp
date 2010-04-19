// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Contains string constants for the most common XML namespace URIs.
var XmlNamespaces = {
  SCHEMA: "http://www.w3.org/1999/XMLSchema",
  XFORMS: "http://www.w3.org/2002/xforms",
  XHTML:  "http://www.w3.org/1999/xhtml",
  XML:    "http://www.w3.org/XML/1998/namespace",
  XSL:    "http://www.w3.org/1999/XSL/Transform",
  EVENTS: "http://www.w3.org/2001/xml-events"
};

// Opera will manhandle elements and attributes in the XHTML and XML Events
// namespaces, so we have to change those namespaces to something else so Opera
// doesn't recognize them. See namespaces.js for the other half of this kludge.
if (userAgent.isOpera) {
  XmlNamespaces.XHTML  += "-in-opera";
  XmlNamespaces.EVENTS += "-in-opera";
}


// Returns the namespace URI for a node, or null if it has none.
//
// Internet Explorer does not import namespace URIs, so we need to resolve them
// manually.
function xmlNamespaceURI(node) {
  assert(node != null, "xmlNamespaceURI: node is null");
  
  if (!userAgent.isInternetExplorer) {
    return node.namespaceURI == null ? "" : node.namespaceURI;
  }
  
  // If the namespace URI is set, then IE obviously resolved the namespace
  // properly.
  if (node.namespaceURI != "") {
    return node.namespaceURI;
  }
  
  // Otherwise, we can't be sure, so we'll have to lookup the namespace URI
  // ourselves.
  var namespaceNodeName = "xmlns";
  
  if (node.nodeName.match(/(.*):/)) {
    namespaceNodeName += ":" + RegExp.$1;
  }
  
  if (node.nodeType == 2) {
    // Attributes with no prefix have no namespace.
    if (!node.nodeName.match(/:/)) {
      return "";
    }
    
    node = XPathAxis.PARENT.filterNode(node);
    node = (node.length == 0) ? null : node[0];
  }
  
  if (node.nodeType != 1) {
    return "";
  }
  
  for (; node != null && node.nodeType == 1; node = node.parentNode) {
    var atts   = node.attributes;
    for (var i = atts.length - 1; i >= 0; --i) {
      var attribute = atts.item(i);
    
      if (attribute.name == namespaceNodeName) {
        return attribute.value;
      }
    }
  }
  
  return "";
};