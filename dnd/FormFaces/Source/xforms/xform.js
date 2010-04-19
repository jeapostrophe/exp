// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


var xform = null;

function XForm(xmlDocument) {
  this.xmlDocument      = xmlDocument;

  this.models           = [];
  this.controls         = [];
  this.actions          = [];
  this.events           = [];

  this.objectsById      = {};
  this.objectsByNode    = [];

  this.bindings         = [];
  this.waitingListeners = [];
};

(function() {
  var start = null;
  var end   = null;

  XForm.startTimer = function() {
    start = new Date().getTime();
  };

  XForm.alertTime = function(message) {
    end   = new Date().getTime();

    alert(message.replace(/%t/g, (end - start) / 1000));
    
    start = new Date().getTime();
  };
}) ();

XForm.initialize = function() {
  //var start = new Date().getTime();
  
  // executeSequentially is used to improve perceived performance by giving a
  // chance for the browser to redraw the page and respond to user input between
  // function calls. It also resets the browser timeouts.
  executeSequentially(
    function() {
      var overlay = document.createElement("div");
      var glass   = document.createElement("div");
      var message = document.createElement("span");

      overlay.id            = "-ff-overlay";
      glass  .style.cssText = "position: absolute; top: 0; left: 0; width: 100%; height: 100%; "
                            + "background: white; opacity: 0.75; filter: alpha(opacity=75); overflow: hidden";
      message.style.cssText = "font: 24pt bold 'Helvetica', sans-serif; background: gray; color: white; "
                            + "padding: 4px 8px; border: 9px double white";

      document.body.appendChild(overlay);
      overlay      .appendChild(glass);
      message      .appendChild(document.createTextNode("Loading..."));
      
      if (userAgent.isInternetExplorer) {
        message.style.position   = "absolute";
        message.style.visibility = "hidden";
        
        setTimeout(function() {
          message.style.top        = ((document.documentElement.clientHeight - message.clientHeight) * 0.40) + "px";
          message.style.left       = ((document.documentElement.clientWidth  - message.clientWidth)  * 0.50) + "px";
          message.style.visibility = "visible";
        }, 1);
        
        overlay.appendChild(message);

        document.body.style.cssText = "position: absolute; top: 0; left: 0; width: 100%; height: 100%; margin: 0";
      }
      else {
        var outside = document.createElement("div");
        var middle  = document.createElement("div");
        var inside  = document.createElement("div");
        
        // Vertical centering courtesy of http://www.jakpsatweb.cz/css/css-vertical-center-solution.html.
        outside.style.cssText = "position: absolute; top: 0; left: 0; width: 100%; height: 100%";
        middle .style.cssText = "display: table; width: 100%; height: 100%; overflow: hidden";
        inside .style.cssText = "display: table-cell; vertical-align: middle; text-align: center";

        overlay.appendChild(outside);
        outside.appendChild(middle);
        middle .appendChild(inside);
        inside .appendChild(message);
      }
    },

    function() {
      // Parse the document.
      if (xform == null) {
        xform = new XForm(xmlLoadURI(window.location.href));
      }
    },

    function() {
      XForm.startTimer();

      new XFormParser().parse(xform.xmlDocument);

      //XForm.alertTime("Parsed in %t seconds.");
    },

    function() {
      xform.render();

      //XForm.alertTime("Page rendered in %t seconds.");
    },

    function() {
      var modelLen = xform.models.length;
      for (var i = 0; i < modelLen; ++i) {
        var model = xform.models[i];

        model.rebuild    ();
        model.recalculate();
        model.revalidate ();
        model.refresh    ();

        XmlEvent.dispatch(model.htmlNode, "xforms-model-construct");
        XmlEvent.dispatch(model.htmlNode, "xforms-model-construct-done");
      }

      //XForm.alertTime("Models rebuilt in %t seconds.");

      for (var i = 0; i < modelLen; ++i) {
        XmlEvent.dispatch(xform.models[i].htmlNode, "xforms-ready");
      }
      
      //alert("Time is: " + (new Date().getTime() - start));
    },

    function() {
      var overlay = document.getElementById("-ff-overlay");
      
      if (overlay != null) {
        document.body.removeChild(overlay);
      }
      
      if (userAgent.isInternetExplorer) {
        document.body.style.cssText = "";//"position: absolute; top: 0; left: 0; width: 100%; height: 100%; margin: 0";
      }
    }
  );
};


XFormParser.prototype.parseXForm = function(element) {
                   this    .parseModels  (element); // XForm.alertTime("Models parsed in %t seconds.");
  xform.controls = this    .parseControls(element); // XForm.alertTime("Controls parsed in %t seconds.");
  xform.actions  = this    .parseActions (element); // XForm.alertTime("Actions parsed in %t seconds.");
  xform.events   = XmlEvent.parseEvents  (element); // XForm.alertTime("Events parsed in %t seconds.");
};


XForm.prototype.render = function() {
  this.renderedNodes = [];

  this.renderHead();
  this.renderBody();
};

// Gets the source XML node for the given rendered HTML node.
//
// Parameters:
//     htmlNode: A rendered HTML node.
//
// Return value:
//     The source XML node.
XForm.prototype.getXmlNode = function(htmlNode) {
  for (var i = this.renderedNodes.length - 1; i >= 0; --i) {
    var renderedNodes = this.renderedNodes[i];

    if (renderedNodes[1] == htmlNode) {
      return renderedNodes[0];
    }
  }

  return null;
};

// Gets the rendered HTML node for the given XForm object or XML node.
//
// Parameters:
//     xmlNode: A node from the XForms source XML document.
//
// Return value:
//     The HTML node that was rendered.
XForm.prototype.getHtmlNode = function(xmlNode) {
  for (var i = this.renderedNodes.length - 1; i >= 0; --i) {
    var renderedNodes = this.renderedNodes[i];

    if (renderedNodes[0] == xmlNode) {
      return renderedNodes[1];
    }
  }

  return null;
};

// Gets the rendered HTML nodes for the given XML node.
//
// Parameters:
//     xmlNode: A node from the XForms source XML document.
//
// Return value:
//     A list of HTML nodes that were rendered.
XForm.prototype.getHtmlNodes = function(xmlNode) {
  var htmlNodes = [];

  for (var i = this.renderedNodes.length - 1; i >= 0; --i) {
    var renderedNodes = this.renderedNodes[i];

    if (renderedNodes[0] == xmlNode) {
      htmlNodes.push(renderedNodes[1]);
    }
  }

  return htmlNodes;
};

XForm.prototype.getObjectForHtmlNode = function(htmlNode) {
  return this.getObjectByNode(this.getXmlNode(htmlNode));
};


XForm.prototype.renderHead = function() {
  var head = document.getElementsByTagName("head")[0];

  // Remove the entire contents of the page body.
  var headChild = head.firstChild;

  while (headChild != null) {
    if (headChild.nodeName.match(/:/)) {
      var badChild = headChild;

      headChild = headChild.nextSibling;

      head.removeChild(badChild);
    }
    else {
      headChild = headChild.nextSibling;
    }
  }

  var modelLen = this.models.length;
  for (var i = 0; i < modelLen; ++i) {
    head.appendChild(this.models[i].render());
  }
};

// Render the XML <body/> to the HTML <body/>.
XForm.prototype.renderBody = function() {
  var htmlBody   = document.body;
  var xmlBody      = null;
  
  for (var child = this.xmlDocument.documentElement.firstChild; child != null; child = child.nextSibling) {
    if (child.nodeType == 1 && child.nodeName.replace(/^.*:/, "") == "body" && child.namespaceURI == XmlNamespaces.XHTML) {
      xmlBody = child;
      break;
    }
  }

  // Remove the entire contents of the page body.
  /* for (var i = 0; i < htmlBody.childNodes.length; ++i) {
    // Don't remove the "Loading..." message.
    if (htmlBody.childNodes.item(i).id == "-ff-overlay") {
      continue;
    }

    htmlBody.removeChild(htmlBody.childNodes.item(i--));
    alert("I = " + i + " ChildNode length: " + htmlBody.childNodes.length);
  } */
  
  var i = htmlBody.childNodes.length - 1;
  while(i > -1) {
    if (htmlBody.childNodes.item(i).id == "-ff-overlay") {
      i--;
      continue;
    }
    
    htmlBody.removeChild(htmlBody.childNodes.item(i--));
  }

  if (xmlBody == null) {
    alert("Unable to load document; <body> not found:\n\n" + xmlSerialize(this.xmlDocument));
    return;
  }

  this.renderChildNodes(xmlBody, htmlBody);

  var controlLen = this.controls.length;
  for (var i = 0; i < controlLen; ++i) {
    var control  = this.controls[i];
    var htmlNode = xform.getHtmlNode(control.xmlNode);

    if (control.getModel() != null) {
      control.getModel().controls.push(control);
    }
    else {
      control.instance = control.instantiate(null, null, 0, htmlNode);
    }
  }
};

XForm.prototype.renderChildNodes = function(xmlParent, htmlParent) {
  for (var xmlChild = xmlParent.firstChild; xmlChild != null; xmlChild = xmlChild.nextSibling) {
    this.renderNode(xmlChild, htmlParent);
  }
};

// Renders a node from the XML source document, inserting a corresponding node
// into the HTML document. XHTML nodes are copied over directly; XForms nodes
// are replaced by placeholder <span/>s. (At this stage, none of the controls
// are rendered properly. That is done when the model is rebuilt.)
//
// Parameters:
//     xmlNode:    The node to render.
//     htmlParent: The parent node for the new HTML node.
//     htmlBefore: The previous sibling for the new HTML node, or null to append
//                 the new node to the end of the parent node. See the DOM
//                 function Node.insertBefore.
XForm.prototype.renderNode = function(xmlNode, htmlParent, htmlBefore) {
  assert(xmlNode    != null, "xmlNode is null");
  assert(htmlParent != null, "htmlParent is null");

  if (typeof(htmlBefore) == "undefined") {
    htmlBefore = null;
  }

  switch (xmlNamespaceURI(xmlNode)) {
    case "":
    case XmlNamespaces.XHTML:
      // Render an HTML node by importing it to the HTML document.
      var htmlNode = xmlImportNode(document, xmlNode, false);

      htmlParent.insertBefore(htmlNode, htmlBefore);

      // If we're rendering a <table/>, and the table has no <tbody/>, add one.
      // Internet Explorer will not render a table without its <tbody/>.
      if (xmlNode.nodeName.replace(/^.*:/, "") == "table" && xmlNode.namespaceURI == XmlNamespaces.XHTML) {
        var tbody = false;
        for (var child = xmlNode.firstChild; child != null; child = child.nextSibling) {
          if (child.nodeType == 1 && child.nodeName.replace(/^.*:/, "") == "tbody" && child.namespaceURI == XmlNamespaces.XHTML) {
            tbody = true;
            break;
          }
        }
        if (!tbody) {
          htmlNode = htmlNode.appendChild(document.createElement("tbody"));
        }
      }

      // Render the children unless this node has XForms attributes (i.e. repeat-bind,
      // repeat-nodeset, etc.).
      var xformsAtt = false;
      var atts = xmlNode.attributes;
      if (atts != null) {
        for (var i = atts.length - 1; i > -1; i--) {
          var att = atts.item(i);
          if (att != null && att.namespaceURI == XmlNamespaces.XFORMS) {
            xformsAtt = true;
            break;
          }
        }
      }
      if (!xformsAtt) {
        this.renderChildNodes(xmlNode, htmlNode);
      }

      break;

    case XmlNamespaces.XFORMS:
      var htmlNode;

      htmlNode           = document.createElement("span");
      htmlNode.className = "xforms-" + xmlNode.nodeName.replace(/^.*:/, "");

      if (xmlNode.attributes.getNamedItem("id") != null) {
        htmlNode.setAttribute("id", xmlNode.attributes.getNamedItem("id").value);
      }

      htmlParent.insertBefore(htmlNode, htmlBefore);
      break;
  }

  this.nodeHasBeenRendered(xmlNode, htmlNode);
};

XForm.prototype.nodeHasBeenRendered = function(xmlNode, htmlNode) {
  var target   = null;
  var events   = this.getEventsFor(xmlNode);
  var eventLen = events.length;

  for (var i = 0; i < eventLen; ++i) {
    (function() {
      var xmlEvent = events[i];
      var handler  = xmlEvent.handler;

      if (!instanceOf(handler, Function)) {
        handler = xform.getObjectByNode(handler);
      }

      new EventListener(htmlNode, xmlEvent.name, xmlEvent.phase, function(event) {
        // If the event target was specified, make sure the event has been fired on that
        // exact target element.
        if (target != null && event.target != target) {
          return;
        }

        if (instanceOf(handler, XFormAction)) {
          handler.execute();
        }
        else {
          handler();
        }

        if (!xmlEvent.defaultAction) {
          event.preventDefault();
        }

        if (!xmlEvent.propagate) {
          event.stopPropagation();
        }
      });
    }) ();
  }

  this.renderedNodes.push([xmlNode, htmlNode]);
};

XForm.prototype.getEventsFor = function(xmlNode) {
  var events   = [];
  var eventLen = this.events.length;

  for (var i = 0; i < eventLen; ++i) {
    if (this.events[i].observer == xmlNode) {
      events.push(this.events[i]);
    }
  }

  return events;
};


// Call this function in the setUpPage() function for each unit test suite to
// ensure that the "xform" object is created before the tests are run.
//
//     function setUpPage() {
//       XForm.waitForInitialization();
//     }
XForm.waitForInitialization = function() {
  new EventListener(document.documentElement, "xforms-ready", "default",
    function () {
      setUpPageStatus = "complete";
    }
  );
};

// Checks if the given node is an XForms element.
//
// Parameters:
//     node:     The node to check.
//     tagNames: Optional. If specified, this can be either the expected tag
//               name for the element (a single string), or a list of expected
//               tag names (an array of strings).
XForm.isXFormsElement = function(node, tagNames) {
  if (node.nodeType != 1 || node.namespaceURI != XmlNamespaces.XFORMS) {
    return false;
  }
  
  if (tagNames == null) {
    return true;
  }
  
  var tagName = node.nodeName.replace(/^.*:/, "");
  
  if (typeof(tagNames) == "string") {
    return tagName == tagNames;
  }
  else {
    for (var i = 0; i < tagNames.length; ++i) {
      if (tagName == tagNames[i]) {
        return true;
      }
    }
    
    return false;
  }
};

// Checks if the given node is an XHTML element.
//
// Parameters:
//     node:     The node to check.
//     tagNames: Optional. If specified, this can be either the expected tag
//               name for the element (a single string), or a list of expected
//               tag names (an array of strings).
XForm.isXHtmlElement = function(node, tagNames) {
  if (node.nodeType != 1 || node.namespaceURI != XmlNamespaces.XHTML) {
    return false;
  }
  
  if (tagNames == null) {
    return true;
  }
  
  var tagName = node.nodeName.replace(/^.*:/, "");
  
  if (typeof(tagNames) == "string") {
    return tagName == tagNames;
  }
  else {
    for (var i = 0; i < tagNames.length; ++i) {
      if (tagName == tagNames[i]) {
        return true;
      }
    }
    
    return false;
  }
};


// Define the initialization events.
XmlEvent.define("xforms-model-construct",      "Events", true, false);
XmlEvent.define("xforms-model-construct-done", "Events", true, false);
XmlEvent.define("xforms-ready",                "Events", true, false);