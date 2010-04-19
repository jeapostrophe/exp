// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new XML document with the specified document element. If
// unspecified, an element called "root" with no namespace is created.
//
// Opera does not allow the creation of a document without a root element, so it
// is not possible to create a completely blank document with this function.
// Furthermore, in Opera you cannot change, rename, or remove the document
// element either.
//
// Parameters:
//     documentElement: The root element of the document. 
function xmlNewDocument(documentElement) {
  if (documentElement == null) {
    documentElement = document.createElement("root");
  }
  
  if (document.implementation && document.implementation.createDocument) {
    var xmlDocument = document.implementation.createDocument(documentElement.namespaceURI, documentElement.tagName, null);
  }
  else if (typeof(window.ActiveXObject) != "undefined") {
    var xmlDocument = xmlNewMSXMLDocument();
  }
  else {
    throw new XmlException("Incompatible web browser; cannot create new XML document.");
  }
  
  if (documentElement) {
    documentElement = xmlImportNode(xmlDocument, documentElement, true);
    
    if (xmlDocument.firstChild) {
      while (documentElement.hasChildNodes()) {
        xmlDocument.firstChild.appendChild(documentElement.firstChild);
      }
      
      var isHtml = (documentElement.tagName.toLowerCase() == "html");
      var atts   = documentElement.attributes;
      
      for (var i = atts.length - 1; i >= 0; --i) {
        var attribute = atts.item(i);

        if (attribute.specified && attribute.value) {
          xmlDocument.firstChild.setAttribute(attribute.name, attribute.value);
          
          if (isHtml && userAgent.isInternetExplorer) {
            // Many attributes don't take effect unless you set them via element.property
            // syntax. Also, some of these properties are named/capitalized differently.
            switch (attribute.name) {
              case "colspan":     xmlDocument.firstChild.colSpan       = attribute.value; break;
              case "rowspan":     xmlDocument.firstChild.rowSpan       = attribute.value; break;
              case "cellspacing": xmlDocument.firstChild.cellSpacing   = attribute.value; break;
              case "cellpadding": xmlDocument.firstChild.cellPadding   = attribute.value; break;
              case "style":       xmlDocument.firstChild.style.cssText = attribute.value; break;
              case "class":       xmlDocument.firstChild.className     = attribute.value; break;
              
              default:
                xmlDocument.firstChild[attribute.name] = attribute.value;
                break;
            }
          }
        }
      }
      
    }
    else {
      xmlDocument.appendChild(documentElement);
    }
  }
  
  return xmlDocument;
};

// Returns an MSXML ActiveX DOM document, trying different program IDs until it
// finds one that works.
function xmlNewMSXMLDocument() {
  var programIds = xmlNewMSXMLDocument.programIds;
  
  while (programIds.length > 0) {
    try {
      return new ActiveXObject(programIds[0]);
    }
    catch (e) {
      // Didn't work. Try the next program.
      programIds.shift();
    }
  }
  
  throw new XmlException("Unable to create new MSXML DOM document.");
};

xmlNewMSXMLDocument.programIds = [
  "Msxml2.DOMDocument.5.0",
  "Msxml2.DOMDocument.4.0",
  "Msxml2.DOMDocument.3.0",
  "MSXML2.DOMDocument",
  "MSXML.DOMDocument",
  "Microsoft.XMLDOM"
];

// Loads an XML document.
//
// Parameters:
//     source:   The source text for the XML document.
//     stripDTD: If true, the DTD is stripped from the document and all entities
//               are replaced by their substitution text.
//
// Return value:
//     An XML DOM document if there are no errors.
//
// Exceptions:
//     Throws an exception if there is an error loading the document.
function xmlLoadDocument(source, stripDTD) {
  if (stripDTD) {
    source = cleanXml(source);
  }
  
  var xmlDocument = null;
  
  // W3C
  if (document.implementation && document.implementation.createLSParser) {
    var parser = document.implementation.createLSParser(1, null);
    var input  = document.implementation.createLSInput ();
    
    // Opera will manhandle elements and attributes in the XHTML and XML Events
    // namespaces, so we have to change those namespaces to something else so Opera
    // doesn't recognize them. See namespaces.js for the other half of this kludge.
    if (userAgent.isOpera) {
      source = source.replace(/(xmlns(?::[^=]+)?=["']http:\/\/www.w3.org\/1999\/xhtml)(["'])/,      "$1-in-opera$2");
      source = source.replace(/(xmlns(?::[^=]+)?=["']http:\/\/www.w3.org\/2001\/xml-events)(["'])/, "$1-in-opera$2");
    }
    
    input.stringData = source;
    
    xmlDocument = parser.parse(input);
  }
  // Mozilla
  else if (window.DOMParser) {
    xmlDocument = new DOMParser().parseFromString(source, "text/xml");
    
     if (xmlDocument.documentElement.namespaceURI == "http://www.mozilla.org/newlayout/xml/parsererror.xml") {
      throw new XmlException(new XPath("string(/*/text())").evaluate(xmlDocument));
    }
  }
  // Internet Explorer
  else if (window.ActiveXObject) {
    xmlDocument = xmlNewMSXMLDocument();
    
    xmlDocument.preserveWhiteSpace = true;
    xmlDocument.loadXML(source);

    if (xmlDocument.parseError.errorCode != 0) {
      throw new XmlException(
        xmlDocument.parseError.reason.replace(/^\s+|\s+$/g, "") + "\n\n" +
        "Line: "   + xmlDocument.parseError.line + "\n" +
        "Source: " + xmlDocument.parseError.srcText.replace(/^\s+|\s+$/g, ""),
        
        xmlDocument.parseError
      );
    }
  }
  else {
    throw new XmlException("Incompatible web browser; cannot load XML document.");
  }
  
  var stylesheets = new XPath("//processing-instruction('xml-stylesheet')").evaluate(xmlDocument);
  
  for (var i = 0; i < stylesheets.length; ++i) {
    var xslUrl      = stylesheets[i].data.replace(/^.*\bhref\s*=\s*"([^"]*)".*$/, "$1");
    var xslDocument = xmlLoadURI(xslUrl);
    
    // XSL stylesheets might use the "html" method, but we need to get a strict XML
    // document, so we'll stealthily change this setting.
    for (var child = xslDocument.documentElement.lastChild; child != null; child = child.previousSibling) {
      if(child.nodeName.replace(/^.*:/, "") == "output" && child.namespaceURI == XmlNamespaces.XSL) {
        child.setAttribute("method", "xml");
      }
    }
    
    // Apply the stylesheet.
    if (userAgent.isMozilla) {
      var xsltProcessor = new XSLTProcessor();
      xsltProcessor.importStylesheet(xslDocument);
      alert("xsltProcessor doesn't like this example.");
      
      xmlDocument = xsltProcessor.transformToDocument(xmlDocument);
    }
    else if (userAgent.isInternetExplorer) {
      xmlDocument = xmlLoadDocument(xmlDocument.transformNode(xslDocument));
    }
    else {
      assert(false, "Cannot load page: XSL stylesheets are not supported in this browser.");
    }
    
  }
  
  return xmlDocument;
  

  // Strips the DTD from the XML source and replaces any entities with their
  // substitution text.
  function cleanXml(source) {
    // Remove any <!DOCTYPE> declarations. Internet Explorer, correctly but
    // unfortunately, validates documents against their DTDs.
    source = source.replace(/<!DOCTYPE[^>]*>/, "");
  
    // Replace entities with their replacement characters since we just removed the
    // <!DOCTYPE>.
    var index = -1;
  
    while (true) {
      var entityIndex = source.indexOf("&",         index + 1);
      var cdataIndex  = source.indexOf("<![CDATA[", index + 1);
      
      if (entityIndex < 0) {
        break;
      }
  
      // If the next ampersand comes before the next CDATA section, it is an entity.
      if (cdataIndex < 0 || entityIndex < cdataIndex) {
        // Returns the replacement character for an entity.
        function entityReplacement(entity) {
          var span           = document.createElement("span");
              span.innerHTML = entity;
              
          return (span.firstChild != null) ? span.firstChild.data : "";
        }
        
        // Replace the entity with the equivalent character.
        var entity = source.substring(entityIndex, source.indexOf(";", entityIndex) + 1);
        
        switch (entity) {
          // Don't substitute the built-in entities; it can cause well-formedness errors.
          case "&amp;":
          case "&lt;":
          case "&gt;":
          case "&quot;": 
          case "&apos;":
            break;
            
          default:
            source = source.replace(entity, entityReplacement(entity));
            break;
        }
        
        index = entityIndex;
      }
      // otherwise, we need to first skip over the CDATA section.
      else {
        index = source.indexOf("]]>", cdataIndex);
        
        if (index < 0) {
          break;
        }
      }
    }
    
    return source;
  };
};

// Loads the document at the requested URI.
//
// Return value:
//     A XML document containing the DOM tree for the document.
//
// Exceptions:
//     Throws an XmlException if there is an error fetching the URI, or if there
//     is an error parsing the XML document.
function xmlLoadURI(uri) {
  //var request = window.XMLHttpRequest ? new XMLHttpRequest() : new ActiveXObject("Microsoft.XMLHTTP");
  var request = userAgent.isInternetExplorer ? new ActiveXObject("Microsoft.XMLHTTP") : new XMLHttpRequest(); 
  
  try {
    request.open("GET", uri, false);
    request.send(null);
  }
  catch (exception) {
    throw new XmlException("Error loading " + uri + ".", exception);
  }
  
  if (request.status != 200 && request.status != 0) {
    throw new XmlException("Error " + request.status + " loading " + uri + ": " + request.statusText);
  }
  
  return xmlLoadDocument(request.responseText, true);
};