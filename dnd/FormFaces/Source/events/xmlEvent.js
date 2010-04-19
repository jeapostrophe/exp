// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new XML event.
//
// Parameters:
//     element:       The element from which the event was created.
//     name:          The name of the event.
//     handler:       The element that will handle the event once it has been caught.
//     target:        The target element of the event, or null if unspecified.
//     observer:      The element that will listen for the event.
//     phase:         The phase during which the listener is to be activated.
//     propagate:     Specifies whether or not the event processing is allowed
//                    to continue after all the listeners have been activated.
//     defaultAction: Specifies whether or not the event's default action is to
//                    take place after all the listeners have been activated.
function XmlEvent(element, name, handler, target, observer, phase, propagate, defaultAction) {
  assert(name     != null, "name is null");
  assert(handler  != null, "handler is null");
  assert(observer != null, "observer is null");

  this.name          = name;
  this.handler       = handler;
  this.target        = target;
  this.observer      = observer;
  this.phase         = phase;
  this.propagate     = propagate;
  this.defaultAction = defaultAction;
};

XmlEvent.parseEvents = function(element) {
  return new XmlEventParser().parseEvents(element);
};


function XmlEventParser() {
};

XmlEventParser.prototype.parseEvents = function(element) {
  var events        = [];
  var self          = this;
  
  if (element.namespaceURI == XmlNamespaces.EVENTS && element.getAttribute("event") != null) {
    events.push(this.parseEvent(element));
  }
  
  var atts = element.attributes;
  var eventAtt = false;
  for (var i = atts.length - 1; i > -1; i--) {
    var att = atts.item(i);
    if (att != null && att.namespaceURI == XmlNamespaces.EVENTS && att.nodeName.replace(/^.*:/, "") == "event") {
      eventAtt = true;
      break;
    }
  }
  if (eventAtt) {
    events.push(this.parseEvent(child));
  }
  
  locateEvents(element);
  
  function locateEvents(element) {
    for (var child = element.firstChild; child != null; child = child.nextSibling) {
      if (child.nodeType == 1) {
        if (child.namespaceURI == XmlNamespaces.EVENTS && element.getAttribute("event") != null) {
          events.push(self.parseEvent(child));
        }
        else {
          var atts = child.attributes;
          var eventAtt = false;
          for (var i = atts.length - 1; i > -1; i--) {
            var att = atts.item(i);
            if (att != null && att.namespaceURI == XmlNamespaces.EVENTS && att.nodeName.replace(/^.*:/, "") == "event") {
              eventAtt = true;
              break;
            }
          }
          if (eventAtt) {
            events.push(self.parseEvent(child));
          }
          else {
            locateEvents(child);
          }
        }
      }
    }
  }
  
  return events;
};

XmlEventParser.prototype.parseEvent = function(element) {
  return new XmlEvent(
    element,
    
    this.parseName         (element),
    this.parseHandler      (element),
    this.parseTarget       (element),
    this.parseObserver     (element),
    this.parsePhase        (element),
    this.parsePropagate    (element) == "continue",
    this.parseDefaultAction(element) == "perform"
  );
};

XmlEventParser.prototype.parseName = function(element) {
  return this.attribute(element, "event");
};

XmlEventParser.prototype.parseHandler = function(element) {
  var uri = this.attribute(element, "handler", null);
  
  if (uri == null) {
    return element;
  }
  
  var id = uri.substr(uri.indexOf("#") + 1);

  if (uri.indexOf("#") == 0) {
    var handler = this.getElementById(element.ownerDocument, id);
    
    if (handler == null) {
      handler = window[id];
    }
    
    return handler;
  }
  else {
    return this.getElementById(xmlLoadURI(uri.substring(0, uri.indexOf("#"))), id);
  }
};

XmlEventParser.prototype.parsePhase = function(element) {
  return this.attribute(element, "phase", "default");
};

XmlEventParser.prototype.parsePropagate = function(element) {
  return this.attribute(element, "propagate", "continue");
};

XmlEventParser.prototype.parseDefaultAction = function(element) {
  return this.attribute(element, "defaultAction", "perform");
};

XmlEventParser.prototype.parseTarget = function(element) {
  var target = this.attribute(element, "target", null);

  if (target == null)  {
    return null;
  }
  
  try {
    return xform.getObjectById(target).xmlElement;
  }
  catch (exception) {
    return new XPath("//*[@id = '" + target + "']").selectNode(document);
  }
};

XmlEventParser.prototype.parseObserver = function(element) {
  var observer = this.attribute(element, "observer", null);
  var handler  = this.attribute(element, "handler",  null);

  if (observer != null) {
    return this.getElementById(element.ownerDocument, observer);
  }
  else if (handler != null) {
    return element;
  }
  else {
    return element.parentNode;
  }
};


XmlEventParser.prototype.attribute = function(element, name, defaultValue) {
  var attribute = null;
  var atts = element.attributes;
  
  if (atts != null) {
    for (var i = atts.length - 1; i > -1; i--) {
      var att = atts.item(i);
      if (att != null && att.nodeName.replace(/^.*:/, "") == name) {
        if (element.namespaceURI == XmlNamespaces.EVENTS ||
            att    .namespaceURI == XmlNamespaces.EVENTS)
        {
          attribute = att;
        }
      }
    }
  }
  
  if (attribute == null) {
    if (typeof(defaultValue) == "undefined") {
      throw new XmlException(
        "<" + element.tagName + "/> element is missing the required @" + name +
        " attribute."
      );
    }
    
    return defaultValue;
  }
  
  return attribute.value;
};

XmlEventParser.prototype.getElementById = function(document, id) {
  assert(document.nodeType == 9, "document.nodeType != 9");
  
  try {
    return xform.getObjectById(id).xmlElement;
  }
  catch (exception) {
    return new XPath("//*[@id = '" + id + "']").selectNode(document);
  }
};