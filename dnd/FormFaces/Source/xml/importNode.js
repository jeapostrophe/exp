// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Implements the Document.importNode DOM method. If the browser implements
// importNode natively, then that implementation is used.
//
// Parameters:
//     xmlDocument: The document to which to import the node.
//     node:        The node to import.
//     deep:        True to import all of the node's children, false to only
//                  import the node and its attributes.
function xmlImportNode(xmlDocument, node, deep) {
  if (typeof(xmlDocument.importNode) != "undefined" && !userAgent.isInternetExplorer) {
    // If using Opera and importing a node to the HTML document, we need to fix the
    // fake "-in-opera" namespace URI used. See loadDocument.js for more information
    // about this.
    if (!(xmlDocument == document && userAgent.isOpera)) {
      return xmlDocument.importNode(node, deep);
    }
  }

  var isHtml  = (xmlDocument.documentElement && xmlDocument.documentElement.tagName.toLowerCase() == "html");
  var newNode = null;

  switch (node.nodeType) {
    case 1: // Element
      if (xmlDocument.createElementNS) {
        newNode = xmlDocument.createElementNS(node.namespaceURI, node.nodeName);
      }
      else {
        newNode = xmlDocument.createElement(node.nodeName);
      }

      var atts   = node.attributes; 
      var attLen = atts.length;
      for (var i = 0; i < attLen; ++i) {
        var attribute = atts.item(i);

        if (attribute.specified && attribute.value) {
          newNode.setAttribute(attribute.name, attribute.value);
          
          if (isHtml && userAgent.isInternetExplorer) {
            // Many attributes don't take effect unless you set them via element.property
            // syntax. Also, some of these properties are named/capitalized differently.
            switch (attribute.name) {
              case "colspan":     newNode.colSpan       = attribute.value; break;
              case "rowspan":     newNode.rowSpan       = attribute.value; break;
              case "cellspacing": newNode.cellSpacing   = attribute.value; break;
              case "cellpadding": newNode.cellPadding   = attribute.value; break;
              case "style":       newNode.style.cssText = attribute.value; break;
              case "class":       newNode.className     = attribute.value; break;
              
              default:
                newNode[attribute.name] = attribute.value;
                break;
            }
          }
        }
      }

      break;

    case 2: // Attribute
      if (xmlDocument.createAttributeNS) {
        newNode = xmlDocument.createAttributeNS(node.namespaceURI, node.name);
      }
      else {
        newNode = xmlDocument.createAttribute(node.name);
      }
    
      newNode.value = node.value;
      break;

    case 3: // Text
      newNode = xmlDocument.createTextNode(node.data.replace(/\s+/g, " "));
      break;

    case 4: // CDATA section
      newNode = xmlDocument.createCDATASection(node.data);
      break;

    case 5: // Entity reference
      newNode = xmlDocument.createEntityReference(node.nodeName);
      break;

    case 7: // Processing instruction
      newNode = xmlDocument.createProcessingInstruction(node.target, node.data);
      break;

    case 8: // Comment
      newNode = xmlDocument.createComment(node.data);
      break;

    case 11: // Document fragment
      newNode = xmlDocument.createDocumentFragment();
      break;

    default:
      throw new XmlException("Cannot import node: " + node.nodeName);
  }

  if (deep) {
    for (var child = node.firstChild; child != null; child = child.nextSibling) {
      newNode.appendChild(xmlImportNode(xmlDocument, child, true));
    }
  }
  
  return newNode;
};

function isTextNode(node) {
  return node.nodeType == 3 || node.nodeType == 4;
};