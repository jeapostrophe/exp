// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function XFormParser() {
  this.bindings = [];
};

XFormParser.prototype.parse = function(xmlDocument) {
  this.parseXForm(xmlDocument.documentElement);
};


XFormParser.prototype.stringValue = function(element, attributeName, defaultValue) {
  assert(element          != null, "element is null");
  assert(element.nodeType == 1,    "element.nodeType != 1");
  assert(attributeName    != "",   'attributeName is ""');
  
  var attribute = element.attributes.getNamedItem(attributeName);
  
  if (attribute != null) {
    return attribute.value;
  }
  else {
    if (typeof(defaultValue) == "undefined") {
      throw new XFormException(
        element,
        
        "<" + element.nodeName + "/> element is missing the required @" + attributeName +
        " attribute."
      );
    }

    return defaultValue;
  }
};

XFormParser.prototype.booleanValue = function(element, attributeName, defaultValue) {
  var value = this.stringValue(element, attributeName, defaultValue);
  
  switch (value) {
    case "true":  case "1": return true;
    case "false": case "0": return false;
    
    case null:              return null;
    
    default:
      throw new XFormException(
        element.attributes.getNamedItem(attributeName),
        
        "@" + attributeName + " attribute on <" + element.tagName +
        '/> does not have a valid boolean value: "' + value + '".'
      );
  }
};

XFormParser.prototype.listValue = function(element, attributeName, defaultList) {
  var value = this.stringValue(element, attributeName, defaultList);
  
  if (value == null) {
    return null;
  }
  
  var list = value
    .replace(/^\s+|\s+$/g, "")
    .replace(/\s+/, " ")
    .split(" ");
    
  if (list.length == 1 && list[0] == "") {
    list = [];
  }
  
  return list;
};

XFormParser.prototype.xpathValue = function(element, attributeName, defaultXPath) {
  var xpath = this.stringValue(element, attributeName, defaultXPath);
  
  if (xpath == null) {
    return null;
  }
  
  try {
    return new XPath(xpath, element);
  }
  catch (exception) {
    throw new XFormException(
      element.attributes.getNamedItem(attributeName),

      "@" + attributeName + " attribute on <" + element.nodeName +
      "/> element is not a valid XPath: " + xpath + ".",
      
      exception
    );
  }
};


XFormParser.prototype.getLabelElement = function(parentElement) {
  var labelElement = parentElement.firstChild;
  
  if (labelElement == null) {
    return null;
  }
  
  while (labelElement.nodeType != 1) {
    labelElement = labelElement.nextSibling;
    
    if (labelElement == null) {
      return null;
    }
  }
  
  if (labelElement.nodeName.replace(/^.*:/, "") != "label" ||
      labelElement.namespaceURI != XmlNamespaces.XFORMS)
  {
    return null;
  }
  
  return labelElement;
};
