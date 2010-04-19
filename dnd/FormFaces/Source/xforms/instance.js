// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function XFormInstance(element, document, source) {
  XFormObject.call(this, element, true);
  
  this.document = document;
  this.source   = source;
  
  this.model    = null;
};

XFormInstance.inherits(XFormObject);


XFormParser.prototype.parseInstances = function(element) {
  var instances        = [];
  
  for (var child = element.firstChild; child != null; child = child.nextSibling) {
    if (child.nodeType == 1 && child.nodeName.replace(/^.*:/, "") == "instance" && child.namespaceURI == XmlNamespaces.XFORMS) {
      instances.push(this.parseInstance(child));
    }
  }
  
  return instances;
};

XFormParser.prototype.parseInstance = function(element) {
  var srcAttribute = element.attributes.getNamedItem("src");
  var instance     = null;
  
  if (srcAttribute != null) {
    instance = new XFormInstance(element, xmlLoadURI(srcAttribute.value), srcAttribute.value);
  }
  else {
    // We can't just use childNodes since that will include text nodes, comments,
    // etc.
    var instanceNodes = new XPath("*").evaluate(element);
    
    switch (instanceNodes.length) {
      case 0:
        instance = new XFormInstance(element, null, null);
        break;
        
      case 1:
        var instanceDocument = xmlNewDocument(instanceNodes[0]);
        var instanceNode     = instanceDocument.documentElement;
        
        // Copy the namespaces visible on the <instance/> element to the instance
        // document root element.
        var namespaceNodes = new XPath("namespace::*").evaluate(instanceNodes[0]);
        
        var namespaces = namespaceNodes.length;
        for (var i = 0; i < namespaces; ++i) {
          var namespaceNode = namespaceNodes[i];
          
          if (namespaceNode.name == "xmlns:xml") {
            continue;
          }
          
          if (!instanceNode.attributes.getNamedItem(namespaceNode.name)) {
            instanceNode.setAttribute(namespaceNode.name, namespaceNode.value);
          }
        }
        
        instance = new XFormInstance(element, instanceDocument, null);
        break;
      
      default:
        throw new XFormException(
          element,
          "<" + element.tagName + "/> contains more than one root element."
        );
    }
  }
  
  while (element.hasChildNodes()) {
    element.removeChild(element.firstChild);
  }
  
  return instance;
};