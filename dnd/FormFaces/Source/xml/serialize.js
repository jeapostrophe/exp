// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Returns the serialized XML string for the specified DOM node.
function xmlSerialize(node, options, filter) {
  assert(node                  != null,        "xmlSerialize: node is null");
  assert(typeof(node.nodeType) != "undefined", "xmlSerialize: node is not a DOM node");
  
  if (typeof(options)                          == "undefined") { options                          = { };     }
  if (typeof(options.standalone)               == "undefined") { options.standalone               = null;    }
  if (typeof(options.encoding)                 == "undefined") { options.encoding                 = "UTF-8"; }
  if (typeof(options.omitXmlDeclaration)       == "undefined") { options.omitXmlDeclaration       = false;   }
  if (typeof(options.includeNamespacePrefixes) == "undefined") { options.includeNamespacePrefixes = null;    }
  if (typeof(options.cdataSectionElements)     == "undefined") { options.cdataSectionElements     = [];      }
  
  if (typeof(filter) != "undefined" && !filter(node)) {
    return "";
  }
  
  switch (node.nodeType) {
    case 1: // Element
      var xml = "<" + node.tagName;
      
      var attributes    = node.attributes;
      var numAttributes = attributes.length;
      
      for (var i = 0; i < numAttributes; ++i) {
        var attribute = attributes.item(i);
        
        // Opera can have null attributes.
        if (attribute == null) {
          continue;
        }
        
        if (attribute.specified) {
          xml += xmlSerialize(attribute, options, filter);
        }
      }
      
      if (node.hasChildNodes()) {
        xml += ">";
      
        for (var child = node.firstChild; child != null; child = child.nextSibling) {
          xml += xmlSerialize(child, options, filter);
        }
        
        xml += "</" + node.tagName + ">";
      }
      else {
        xml += "/>";
      }
      
      return xml;
      
    case 2: // Attribute
      // Namespace node.
      if (node.name.match(/^xmlns(:|$)/) && !isVisiblyUtilized(node)) {
        return "";
      }
      
      var name  = node.name;
      var value = node.value.replace(/&/g, "&amp;")
                            .replace(/"/g, "&quot;")
                            .replace(/</g, "&lt;")
                            .replace(/>/g, "&gt;");
                            
      if (value.indexOf("function(") == 0) {
        value = "<function>";
      }
        
      return " " + name + '="' + value + '"';
      
    case 3: // Text
      if (isCDataSectionElement(node.parentNode)) {
        // Fall through to CDATA case.
      }
      else {
        return node.data.replace(/&/g, "&amp;")
                        .replace(/</g, "&lt;")
                        .replace(/>/g, "&gt;");
      }
      
    case 4: // CDATA section
      return "<![CDATA[" + node.data.replace(/]]>/g, "]]]]><![CDATA[>") + "]]>";
      
    case 7: // Processing instruction
      return "<?" + node.target + " " + node.data + "?>";
      
    case 8: // Comment
      return "<!--" + node.data + "-->";  
      
    case 9: // Document
      var xml = "";
      
      if (!options.omitXmlDeclaration) {
        var encoding   = (options.encoding   == "UTF-16") ? "UTF-16" : "UTF-8";
        var standalone = (options.standalone != null)     ? ' standalone="' + (options.standalone ? "yes" : "no") + '"' : "";
        
        xml += '<?xml version="1.0" encoding="' + encoding + '"' + standalone + '?>\n\n';
      }
    
      for (var child = node.firstChild; child != null; child = child.nextSibling) {
        xml += xmlSerialize(child, options, filter) + "\n";
      }
      
      return xml;
      
    case 10: // Document type
      var xml = "<!DOCTYPE " + node.name + ' PUBLIC "' + node.publicId + '" "' + node.systemId + '" [\n';
      
      xml += "]>";
      
      return xml;
      
    case 11: // Document fragment
      var xml = "";
    
      for (var child = node.firstChild; child != null; child = child.nextSibling) {
        xml += xmlSerialize(child, options, filter);
      }
      
      return xml;
      
    default:
      assert(false, "Unsupported node: " + node.nodeName + " (" + node.nodeType + ")");
  }


  function isVisiblyUtilized(namespaceNode) {
    // If includeNamespacePrefixes is null, serialize all namespace nodes.
    if (!options.includeNamespacePrefixes) {
      return true;
    }
    
    var prefix  = namespaceNode.name.substring(6);
    var element = new XPath("..").selectNode(namespaceNode);
    var namespaceLen = options.inlcudeNamespacePrefixes.length;
    
    // If the prefix is in includeNamespacePrefixes, serialize it.
    for (var i = 0; i < namespaceLen; ++i) {
      var includePrefix = options.includeNamespacePrefixes[i];
      
      if (includePrefix == prefix || includePrefix == "#default" && prefix == "") {
        return true;
      }
    }
    
    // Check that the namespace prefix is visibly utilized based on the Exclusive
    // XML Canonicalization specification.
    if (namespaceNode.name == "xmlns") {
      return element.prefix == null;
    }
    else {
      return new XPath("parent::" + prefix + ":* or ..//@" + prefix + ":*").evaluate(namespaceNode);
    }
  };
  
  function isCDataSectionElement(element) {
    var cdataLen = options.cdataSectionElements.length;
    for (var i = 0; i < cdataLen; ++i) {
      if (options.cdataSectionElements[i].matches(element)) {
        return true;
      }
    }
    
    return false;
  };
};