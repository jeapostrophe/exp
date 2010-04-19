// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new QName, which is a namespace URI and local name pair.
//
// Parameters:
//     namespaceURI: A namespace URI.
//     localName:    A local name.
function QualifiedName(namespaceURI, localName) {
  if (arguments.length == 0) {
    return;
  }
  
  this.namespaceURI = namespaceURI;
  this.localName    = localName;
};

// Compares the QName against the specified node's name.
//
// Return value:
//     True if the node's name matches the QName, false if not.
QualifiedName.prototype.matches = function(node) {
  var localName    = node.nodeName.replace(/^.*:/, "");
  var namespaceURI = xmlNamespaceURI(node);
  
  // Opera will give attributes the namespace of their owner element. Reverse that.
  if (userAgent.isOpera && node.nodeType == 2) {
    if (namespaceURI != "" && namespaceURI == xmlNamespaceURI(node.ownerElement)) {
      namespaceURI = "";
    }
  }
  
  return localName    == this.localName
      && namespaceURI == this.namespaceURI;
};

// Returns a string like either local-name or {namespace-uri}local-name.
QualifiedName.prototype.toString = function() {
  return this.namespaceURI == ""
    ? this.localName
    : "{" + this.namespaceURI + "}" + this.localName;
};