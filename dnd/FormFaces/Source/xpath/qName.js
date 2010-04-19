// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new QName, which is a namespace URI and local name pair.
//
// Parameters:
//     qName:       The QName string, either "name" or "ns:name".
//     contextNode: The context node from which to resolve the QName's namespace
//                  prefix, if it has one.
function QName(qName, contextNode) {
  var parts = qName.split(":");
  
  if (parts.length == 2) {
    var namespaceURI = QName.lookupNamespaceURI(contextNode, parts[0]);
    var localName    = parts[1];
    
    // Prefixes are not allowed to map to the default namespace.
    if (namespaceURI == "") {
      throw new XPathInvalidPrefixException(contextNode, parts[0]);
    }
  }
  else {
    var namespaceURI = "";
    var localName    = qName;
  }
  
  QualifiedName.call(this, namespaceURI, localName);
};

QName.inherits(QualifiedName);

// Looks up the namespace URI for a prefix at the specified context node.
QName.lookupNamespaceURI = function(contextNode, prefix) {
  if (prefix == "xml") {
    return XmlNamespaces.XML;
  }
  
  for (var node = contextNode; node != null && node.attributes != null; node = node.parentNode) {
    var atts      = node.attributes;
    var attLength = atts.length;
    for (var i = 0; i < attLength; ++i) {
      var attribute = atts.item(i);
    
      if (attribute.name == "xmlns:" + prefix) {
        return attribute.value;
      }
    }
  }
  
  return "";
};