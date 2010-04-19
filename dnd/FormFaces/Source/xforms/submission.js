// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new submission object.
//
// Parameters:
//     element: The element from which the submission was created.
//
//     bind: The submission's bind.
//
//     action: The action URI.
//
//     method: The submission method. One of "post", "put", "get",
//         "multi-part-post", "form-data-post", or "urlencoded-post".
//
//     version: The XML version to be serialized, or null to leave it
//         unspecified.
//
//     indent: Value specifying whether the serializer should add extra white
//         space nodes for readability.
//
//     mediaType: The media type for XML serialization. The type specified must
//         be compatible with application/xml.
//
//     encoding: The character encoding for serialization, or null to leave it
//         unspecified.
//
//     omitXmlDeclaration: Value specifying whether to omit the XML declaration
//         on the serialized instance data or not.
//
//     standalone: Value specifying whether to include a standalone declaration
//         in the serialized XML or not.
//
//     cdataSectionElements: A list of element names to be serialized with CDATA
//         sections.
//
//     replace: Value specifying how the information returned after submit
//         should be applied. One of "all", "instance", or "none".
//
//     separator: The separator character between name/value pairs in URL-
//         encoding.
//
//     includeNamespacePrefixes: If null, all namespace nodes present in the
//         instance data are considered for serialization. Otherwise, specifies
//         a list of namespace prefixes to consider for serialization, in
//         addition to those visibly utilized.
function XFormSubmission(element, bind, action, method, version, indent,
                         mediaType, encoding, omitXmlDeclaration, standalone,
                         cdataSectionElements, replace, separator,
                         includeNamespacePrefixes)
{
  assert(bind                 != null, "submission: bind is null");
  assert(action               != null, "submission: action is null");
  assert(method               != null, "submission: method is null");
  assert(mediaType            != null, "submission: mediaType is null");
  assert(cdataSectionElements != null, "submission: cdataSectionElements is null");

  XFormObject.call(this, element, true);
  
  this.bind                     = bind;
  this.action                   = action;
  this.method                   = method;
  this.mediaType                = mediaType;
  this.replace                  = replace;
  this.separator                = separator;
  this.version                  = version;
  this.indent                   = indent;
  this.encoding                 = encoding;
  this.omitXmlDeclaration       = omitXmlDeclaration;
  this.standalone               = standalone;
  this.cdataSectionElements     = cdataSectionElements;
  this.includeNamespacePrefixes = includeNamespacePrefixes;

  this.model = null;
};

XFormSubmission.inherits(XFormObject);


XFormParser.prototype.parseSubmissions = function(element) {
  var submissions        = [];
  
  for (var child = element.firstChild; child != null; child = child.nextSibling) {
    if (child.nodeType == 1 && child.nodeName.replace(/^.*:/, "") == "submission" && child.namespaceURI == XmlNamespaces.XFORMS) {
      submissions.push(this.parseSubmission(child));
    }
  }
  
  return submissions;
};

XFormParser.prototype.parseSubmission = function(element) {
  return new XFormSubmission(
    element,
    
    this.parseSubmissionBind                    (element),
    this.parseSubmissionAction                  (element),
    this.parseSubmissionMethod                  (element),
    this.parseSubmissionVersion                 (element),
    this.parseSubmissionIndent                  (element),
    this.parseSubmissionMediaType               (element),
    this.parseSubmissionEncoding                (element),
    this.parseSubmissionOmitXmlDeclaration      (element),
    this.parseSubmissionStandalone              (element),
    this.parseSubmissionCDataSectionElements    (element),
    this.parseSubmissionReplace                 (element),
    this.parseSubmissionSeparator               (element),
    this.parseSubmissionIncludeNamespacePrefixes(element)
  );
};

XFormParser.prototype.parseSubmissionBind = function(element) {
  var bindAttribute = element.attributes.getNamedItem("bind");
  
  if (bindAttribute != null) {
    return xform.getObjectById(bindAttribute);
  }
  else {
    return new XFormBind(element, "ref", this.xpathValue(element, "ref", "/"), null, []);
  }
};

XFormParser.prototype.parseSubmissionAction = function(element) {
  return this.stringValue(element, "action");
};

XFormParser.prototype.parseSubmissionMethod = function(element) {
  var method = this.stringValue(element, "method");

  switch (method) {
    case "post":
    case "put":
    case "get":
    case "multi-part-post":
    case "form-data-post":
    case "urlencoded-post":
      return method;

    default:
      throw new XFormException(
        element.attributes.getNamedItem("method"),
        "<" + element.tagName + '/> element has an invalid @method: "' + method + '".'
      );
  }
};

XFormParser.prototype.parseSubmissionVersion            = function(element) { return this.stringValue (element, "version",              null);              };
XFormParser.prototype.parseSubmissionIndent             = function(element) { return this.booleanValue(element, "indent",               "false");           };
XFormParser.prototype.parseSubmissionMediaType          = function(element) { return this.stringValue (element, "mediatype",            "application/xml"); };
XFormParser.prototype.parseSubmissionEncoding           = function(element) { return this.stringValue (element, "encoding",             null);              };
XFormParser.prototype.parseSubmissionOmitXmlDeclaration = function(element) { return this.booleanValue(element, "omit-xml-declaration", "false");           };
XFormParser.prototype.parseSubmissionStandalone         = function(element) { return this.booleanValue(element, "standalone",           "false");           };

XFormParser.prototype.parseSubmissionCDataSectionElements = function(element) {
  var elementNames = this.listValue(element, "cdata-section-elements", "");
  var elements     = [];

  var names = elementNames.length;
  for (var i = 0; i < names; i++) {
    elements.push(new QName(elementNames[i], element));
  }
  
  return elements;
};

XFormParser.prototype.parseSubmissionReplace = function(element) {
  var replace = this.stringValue(element, "replace", "all");

  switch (replace) {
    case "all":
    case "instance":
    case "none":
      return replace;

    default:
      throw new XFormException(
        element.attributes.getNamedItem("replace"),
        '<' + element.tagName + '/> has invalid value for @replace: "' + replace + '".'
      );
  }
};

XFormParser.prototype.parseSubmissionSeparator = function(element) {
  return this.stringValue(element, "separator", ";");
};

XFormParser.prototype.parseSubmissionIncludeNamespacePrefixes = function(element) {
  var prefixes = this.listValue(element, "includenamespaceprefixes", null);
  
  if (prefixes == null) {
    return null;
  }

  var allPrefixes = prefixes.length;
  for (var i = 0; i < allPrefixes; i++) {
    if (prefixes[i] == "#default") {
      prefixes[i] = "";
    }
  }

  return prefixes;
};


XFormSubmission.prototype.submit = function() {
  var graph       = this.model.graph;
  var boundNode   = this.bind.defaultBinding.boundNodes[0];
  var boundVertex = graph.getVertex(boundNode, "text");
  
  if (!boundVertex.isValid) {
     status("Bound vertex node is not valid!: " + boundNode + " :: " + boundVertex);
     XmlEvent.dispatch(this.htmlNode, "xforms-submit-error");
     return;
  }
  
  var method = {
    "post":            "POST",
    "get":             "GET",
    "put":             "PUT",
    "multipart-post":  "POST",
    "form-data-post":  "POST",
    "urlencoded-post": "POST"
  } [this.method];
  
  switch (this.method) {
    case "post":
    case "put":
      // 
      var content = xmlSerialize(boundNode, this, function(node) {
        var vertex = graph.getVertex(node, "relevant");
        
        return !vertex || vertex.value;
      });
      
      break;
    
    case "get":
    case "urlencoded-post":
      var elements      = new XPath("descendant-or-self::*[count(node()) = 1 and text()]").evaluate(boundNode);
      var relevantNodes = [];
      var content       = "";
      
      for (var i = 0; i < elements.length; ++i) {
        var vertex = graph.getVertex(elements[i], "relevant");
        
        if (!vertex || vertex.value) {
          relevantNodes.push(elements[i]);
        }
      }
      
      for (var i = 0; i < relevantNodes.length; ++i) {
        if (i > 0) {
          content += this.separator;
        }
        
        content += relevantNodes[i].nodeName.replace(/^.*:/, "");
        content += "=";
        content += escape(relevantNodes[i].firstChild.data);
      }
      
      break;
      
    default:
      assert(false, this.method + " submission method not yet implemented.");
  }
  
  //var request = window.XMLHttpRequest ? new XMLHttpRequest() : new ActiveXObject("Microsoft.XMLHTTP");
  var request = userAgent.isInternetExplorer ? new ActiveXObject("Microsoft.XMLHTTP") : new XMLHttpRequest(); 
  var self    = this;
  
  request.onreadystatechange = functionCall(monitor, function() {
    if (request.readyState != 4) {
      return;
    }
    
    status("Response: " + request.status + " " + request.statusText);
    status("Headers:  " + (request.getAllResponseHeaders() != null ? request.getAllResponseHeaders() : ""));
    status("Content:  " + request.responseText);
      
    // 200 is the HTTP success status code. 0 is the status code for local files.
    if (request.status != 200 && request.status != 0) {
      status("Status code is = " + request.status);
      XmlEvent.dispatch(self.htmlNode, "xforms-submit-error");
      return;
    }
    
    if (request.responseText != "" && self.replace != "none") {
      switch (self.replace) {
        case "instance":
          try {
            // Check that the response body is XML.
            var contentType = request.getResponseHeader("Content-Type");
            
            if (!contentType.match(/(^$|[\/+]xml(;.*)?$)/)) {
              status("Non-XML content type: " + contentType);
              
              XmlEvent.dispatch(self.htmlNode, "xforms-submit-error");
              return;
            }
            
            var responseXml = xmlLoadDocument(request.responseText, true);
                  
            if (boundNode.nodeType == 9) {
              boundNode = boundNode.documentElement;
            }
            
            // If replacing the entire document, don't use replaceChild as that doesn't work in Opera.
            if (boundNode == boundNode.ownerDocument.documentElement) {
              // Find the instance boundNode is from and replace its XML document.
              var instances = self.model.instances.length;
              for (var i = 0; i < instances; i++) {
                var instance = self.model.instances[i];
                
                if (instance.document == boundNode.ownerDocument) {
                  instance.document = responseXml;
                  break;
                }
              }
            }
            else {
              var responseNode = xmlImportNode(boundNode.ownerDocument, responseXml.documentElement, true);
              
              boundNode.parentNode.replaceChild(responseNode, boundNode);
            }
            
            XmlEvent.dispatch(self.bind.model.htmlNode, "xforms-rebuild");
            XmlEvent.dispatch(self.bind.model.htmlNode, "xforms-recalculate");
            XmlEvent.dispatch(self.bind.model.htmlNode, "xforms-revalidate");
            XmlEvent.dispatch(self.bind.model.htmlNode, "xforms-refresh");

            break;
          }
          catch (exception) {
            status("Exception thrown during submission: " + exception);
            XmlEvent.dispatch(self.htmlNode, "xforms-submit-error");
            return;
          }
          
        case "all":
          try {
            var responseXml = xmlLoadDocument(request.responseText, true);
            
            if (new XPath("boolean(xhtml:html)").evaluate(responseXml)) {
              xform = new XForm(responseXml);
              XForm.initialize();
              
              break;
            }
            
            status("Response is valid XML but not XHTML.");
          }
          catch (exception) {
            status("Failed to parse response as XML (" + exception + ").");
          }
          var head = request.responseText.replace(/[\s\S]*<head[\s\S]?>/i,   "")
                                         .replace(/<\/head[\s\S]?>[\s\S]*/i, "");
          var body = request.responseText.replace(/[\s\S]*<body[\s\S]?>/i,   "")
                                         .replace(/<\/body[\s\S]?>[\s\S]*/i, "");
                                         
          if (userAgent.isInternetExplorer) {
            document.body.innerHTML = body;
          }
          else {
            while (document.documentElement.hasChildNodes()) {
              document.documentElement.removeChild(document.documentElement.firstChild);
            }
          
            document.documentElement.appendChild(document.createElement("head"));
            document.documentElement.appendChild(document.createElement("body"));
            
            document.documentElement.childNodes[0].innerHTML = head;
            document.documentElement.childNodes[1].innerHTML = body;
          }
          status(xmlSerialize(document));
          break;
          
        default:
          assert(false, 'Unrecognized replace option: "' + self.replace + '".');
      }
    }
    
    XmlEvent.dispatch(self.htmlNode, "xforms-submit-done");
  });
  
  try {
    var url = this.action;
    
    if (method == "GET" && content != "") {
      url    += (url.match(/\?/) ? "&" : "?");
      url    += content;
      
      content = "";
    }
    
    status("Request: " + method + " " + url);
    status("Content: " + content);
    
    request.open            (method, url);
    request.setRequestHeader("Content-Type", this.mediaType);
    request.setRequestHeader("If-Modified-Since", "Thu, 1 Jan 1970 00:00:00 GMT");
    request.send            (content);
  }
  catch (exception) {
    status("Unable to submit form to URL " + this.action + ".");

    XmlEvent.dispatch(self.htmlNode, "xforms-submit-error");
  }
};


XmlEvent.define("xforms-submit", "Events", true, true, function(event) {
  xform.getObjectForHtmlNode(event.target).submit();
});

XmlEvent.define("xforms-submit-done",  "Events", true, false);
XmlEvent.define("xforms-submit-error", "Events", true, false);