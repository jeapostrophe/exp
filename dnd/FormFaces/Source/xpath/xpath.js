// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new XPath.
//
// Parameters:
//     source:      The XPath string from which the XPath was created.
//     contextNode: An XML node from which to lookup the namespace URIs for the
//                  namespace prefixes in the XPath expression.
function XPath(source, contextNode) {
  if (typeof(contextNode) == "undefined") {
    contextNode = XPath.DEFAULT_PREFIXES;
  }
  
  this.source     = source;
  this.expression = XPath.PARSER.parse(source, contextNode);
};

XPath.PARSER = new XPathParser();

XPath.DEFAULT_PREFIXES = xmlNewDocument().createElement("default-prefixes");

XPath.DEFAULT_PREFIXES.setAttribute("xmlns:xfm",    XmlNamespaces.XFORMS);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:xf",     XmlNamespaces.XFORMS);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:xforms", XmlNamespaces.XFORMS);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:form",   XmlNamespaces.XFORMS);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:html",   XmlNamespaces.XHTML);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:xhtml",  XmlNamespaces.XHTML);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:events", XmlNamespaces.EVENTS);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:event",  XmlNamespaces.EVENTS);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:ev",     XmlNamespaces.EVENTS);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:xs",     XmlNamespaces.SCHEMA);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:xsd",    XmlNamespaces.SCHEMA);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:schema", XmlNamespaces.SCHEMA);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:xsl",    XmlNamespaces.XSL);
XPath.DEFAULT_PREFIXES.setAttribute("xmlns:xslt",   XmlNamespaces.XSL);

// Evaluates the XPath starting with the given context or context node.
//
// Parameters:
//     context: The context or context node at which to start evaluation.
//
// Return value:
//     The result of the XPath, which is either a string, number, boolean, or
//     node-set.
XPath.prototype.evaluate = function(context) {
  // If a node was passed as the context, turn it into a full context object.
  if (!instanceOf(context, XPathContext)) {
    context = new XPathContext(context, 1, 1);
  }
  
  return this.expression.evaluate(context);
};

// Evaluates the XPath starting with the given context or context node and
// returns the first node in the result node-set.
// 
// Parameters:
//     context: The context or context node at which to start evaluation.
//
// Return value:
//     The first node from the result node-set, or null if the result node-set
//     is empty.
XPath.prototype.selectNode = function(context) {
  var nodeSet = this.evaluate(context);
  
  if (nodeSet.length == 0) {
    return null;
  }
  else {
    return nodeSet[0];
  }
};

// Determines the nodes that this XPath refers to when evaluated starting with
// the given context or context node.
//
// Parameters:
//     context: The context or context node from which to evaluate the XPath.
//
// Return value:
//     The nodes referred to during evaluation.
XPath.prototype.referencedNodes = function(context) {
  // If a node was passed as the context, turn it into a full context object.
  if (!instanceOf(context, XPathContext)) {
    context = new XPathContext(context, 1, 1);
  }

  return this.expression.referencedNodes(context);
};

// Returns the source string for the XPath.
XPath.prototype.toString = function() {
  return this.source;
};