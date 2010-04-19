// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.

var classNames = {
    "readOnly":   ["xforms-read-write", "xforms-read-only"],
    "required":   ["xforms-optional",   "xforms-required"],
    "relevant":   ["xforms-disabled",   "xforms-enabled"],
    "constraint": ["xforms-invalid",    "xforms-valid"]
  };

// Base class for all controls.
//
// Parameters:
//     element:    The element from which the control was created.
//     bind:       The control's bind, or null if it is unbound.
//     label:      The control's label, or null if it has none.
//     appearance: The appearance of the control.
function XFormControl(element, bind, innerControls, appearance) {
  if (arguments.length == 0) {
    return;
  }

  assert(element != null, "element is null");
  
  XFormObject.call(this, element, true);

  this.bind           = bind;
  this.label          = null;
  this.innerControls  = innerControls;
  this.appearance     = appearance;
  
  this.enclosedBy     = null;
  this.activeInstance = null;
  
  var innerControlsLength = this.innerControls.length;
  
  for (var i = 0; i < innerControlsLength; i++) {
    assert(this.innerControls[i].enclosedBy == null, "enclosedBy is not null");
           this.innerControls[i].enclosedBy = this;
  }
};

XFormControl.inherits(XFormObject);

XFormControl.prototype.getModel = function() {
  if (this.bind != null) {
    return this.bind.model;
  }
  
  if (this.enclosedBy != null && this.enclosedBy.getModel() != null) {
    return this.enclosedBy.getModel();
  }
  
  if (instanceOf(this, XFormOutputControl) && this.value != null) {
    return xform.models[0];
  }
  
  return null;
};

// Returns an XFormControlInstance based on this control. Derived classes must
// implement createInstance(). Callers should call instantiate() and not
// createInstance().
XFormControl.prototype.instantiate = function(enclosingControlInstance, outerBinding, position, htmlNode) {
  var binding = null;
  
  // Get the binding for a bound control.
  if (this.bind != null) {
    if (outerBinding == null) {
      binding = this.bind.model.bindings[this.bind.index];
    }
    else {
      assert(this.bind.outerBind == outerBinding.bind, "outer binds don't match");
      
      binding = outerBinding.innerBindings[position][this.bind.index];
    }
  }
  // <output value="..."/>
  else if (instanceOf(this, XFormOutputControl) && this.value != null) {
    var model            = (outerBinding != null) ? outerBinding.bind.model : xform.models[0];
    
    var valueNode        = document.createElement("output-value");
    var calculateContext = (outerBinding != null)
                             ? new XPathContext(outerBinding.boundNodes[position], position + 1, outerBinding.boundNodes.length)
                             : new XPathContext(model.instances[0].document.documentElement, 1, 1);
    var referencedNodes  = this.value.referencedNodes(calculateContext);
                         
    var textVertex       = model.graph.addVertex(valueNode, "text");
    var calculateVertex  = model.graph.addVertex(valueNode, "calculate", calculateContext, this.value);
                         
    var binding          = new XFormBinding(model, null, new NodeSet([valueNode]), []);
    
    var refNodes         = referencedNodes.length;
    for (var i = 0; i < refNodes; ++i) {
      calculateVertex.dependsOn(model.graph.addVertex(referencedNodes[i], "text"));
    }
    
    textVertex.dependsOn(calculateVertex);                    
  }
  
  var instance = this.createInstance(binding, htmlNode, outerBinding, position);
  
  instance.enclosedBy = enclosingControlInstance;
  
  if (this.activeInstance == null) {
    this.activeInstance = instance;
  }
  
  // Set default control properties before we add the event listeners.
  instance.setProperty("readOnly",   false);
  instance.setProperty("required",   false);
  instance.setProperty("relevant",   true);
  instance.setProperty("constraint", true);
  
  // Dispatch events when MIP values change.
  instance.addListener("readOnly",   function(control, property, value) { XmlEvent.dispatch(instance.htmlNode, value ? "xforms-readonly" : "xforms-readwrite"); });
  instance.addListener("required",   function(control, property, value) { XmlEvent.dispatch(instance.htmlNode, value ? "xforms-required" : "xforms-optional");  });
  instance.addListener("relevant",   function(control, property, value) { XmlEvent.dispatch(instance.htmlNode, value ? "xforms-enabled"  : "xforms-disabled");  });
  instance.addListener("constraint", function(control, property, value) { XmlEvent.dispatch(instance.htmlNode, value ? "xforms-valid"    : "xforms-invalid");   });

  // If the control is bound to an empty node-set, it is non-relevant.
  if (binding != null && binding.boundNodes.length == 0) {
    instance.setProperty("relevant", false);
  }
  
  var boundNodes = (binding != null ? binding.boundNodes.length : 1);
  
  for (var i = 0; i < boundNodes; ++i) {
    if (instance.container != undefined) {
      xform.renderChildNodes(this.xmlNode, instance.container);
    }
	
    instance.innerControlInstances[i] = [];
    
    var innerControlsLength = this.innerControls.length;
    
    for (var j = 0; j < innerControlsLength; j++) {
      var control = this.innerControls[j];
      
      // If this control is not tied to a model but the inner control is, don't
      // instantiate the inner control. It will be instantiated once the model has
      // been initialized.
      if (this.getModel() == null && control.getModel() != null) {
        control.getModel().controls.push(control);
      }
      else {
        var htmlNode = null;
        
        if (control == "label") {
          if (this == "repeat" || this == "switch" || this == "label") {
            htmlNode = instance.container;
          }
          else {
            htmlNode = document.createElement("span");
          }
        }
        else {
          htmlNode = xform.getHtmlNode(control.xmlNode);
        }
        
        control.instance = control.instantiate(instance, instance.nearestBinding, i, htmlNode);
        instance.innerControlInstances[i][j] = control.instance;
      }
    }
  }
  
  instance.postInstantiate();
  
  return instance;
};

// Returns an XFormControlInstance based on this control. Derived classes must
// implement this method. Callers, however, should call instantiate(), not
// createInstance().
XFormControl.prototype.createInstance = function(binding, htmlNode, outerBinding) {
  assert(false, "createInstance not implemented");
};

XFormParser.prototype.parseControls = function(element) {
  var controls = [];
  
  getInnerXFormsElements(this, controls, element);;

  return controls;
  
  
  function getInnerXFormsElements(parser, controls, element) {
    for (var child = element.firstChild; child != null; child = child.nextSibling) {
      if (child.nodeType == 1) {
        if (child.namespaceURI == XmlNamespaces.XFORMS) {
          switch (child.nodeName.replace(/^.*:/, "")) {
            case "label":    
              var parentName = element.nodeName.replace(/^.*:/, "");
              if(parentName != "repeat" && parentName != "switch") {
                controls.push(parser.parseLabel(child));
              }
              break;
            case "input":    controls.push(parser.parseInputControl   (child)); break;
            case "textarea": controls.push(parser.parseTextAreaControl(child)); break;
            case "secret":   controls.push(parser.parseSecretControl  (child)); break;
            case "output":   controls.push(parser.parseOutputControl  (child)); break;
            case "select":
            case "select1":  controls.push(parser.parseSelectControl  (child)); break;
            case "trigger":  controls.push(parser.parseTriggerControl (child)); break;
            case "group":    controls.push(parser.parseGroupControl   (child)); break;
            case "repeat":   controls.push(parser.parseRepeatControl  (child)); break;
            case "switch":   controls.push(parser.parseSwitchControl  (child)); break;
            case "submit":   controls.push(parser.parseSubmitControl  (child)); break;
          }
        }
        else {
          var hasXFormsAttribute = false;
          var attributes         = child.attributes;
          
          for (var i = attributes.length - 1; i >= 0; --i) {
            var att = attributes.item(i);
            
            if (att != null && att.namespaceURI == XmlNamespaces.XFORMS) {
              hasXFormsAttribute = true;
              break;
            }
          }
          
          if (hasXFormsAttribute) {
            controls.push(parser.parseRepeatControl(child));
          }
          else {
            getInnerXFormsElements(parser, controls, child);
          }
        }
      }
    }
    
    return controls;
  };
};

XFormParser.prototype.parseUiInline = function(element) {
  var controls = [];
  var i        = 0;

  for (var child = element.firstChild; child != null; child = child.nextSibling) {
    if (XForm.isXFormsElement(child, "output")) {
      controls[i] = this.parseOutputControl(child);
      ++i;
    }
  }

  return controls;
};

XFormParser.prototype.parseUiCommon = function(element) {
  this.parseActions(element);
};

XFormParser.prototype.parseIncremental = function(element, defaultValue) {
  return this.booleanValue(element, "incremental", defaultValue ? "true" : "false");
};

XFormParser.prototype.parseAppearance = function(element, defaultValue) {
  return this.stringValue(element, "appearance", defaultValue);
};


// Parameters:
//     control: The control that was rendered.
//     binding: The XFormBinding to which the rendered control is bound, or null
//              if the control is unbound.
function XFormControlInstance(control, binding, htmlNode, outerBinding, position) {
  if (arguments.length == 0) {
    return;
  }
  
  assert(control  != null, "control is null");
  assert(htmlNode != null, "htmlNode is null");
  
  XFormObject.call(this, control.xmlNode, false);
  
  this.control        = control;
  this.binding        = binding;
  this.htmlNode       = htmlNode;
  this.outerBinding   = outerBinding;
  
  this.nearestBinding = this.binding && this.binding.bind ? this.binding : this.outerBinding;
  this.position       = this.binding ? 0 : position;
	
	this.innerControlInstances = [];

  // Register the control instance with all of the vertices in the dependency
  // graph to which it is bound so it'll have its relevance/validity/etc. updated
  // when the instance data changes.
  if (this.binding != null) {
    var properties = ["text", "readOnly", "required", "relevant", "constraint"];
    for (var i = this.binding.boundNodes.length - 1; i >= 0; --i) {
      for (var j = properties.length; j >= 0; --j) {
        var vertex = this.binding.model.graph.getVertex(this.binding.boundNodes[i], properties[j]);
        
        if (vertex != null) {
          vertex.controls.push(this);
        }
      }
    }
  }
  
  // For each property, a list of functions to call whenever that property
  // changes.
  this.listeners = {
    "text":       [],
    "readOnly":   [],
    "relevant":   [],
    "required":   [],
    "constraint": []
  };
};

XFormControlInstance.inherits(XFormObject);

XFormControlInstance.prototype.getLabelElement = function() {
  var labelElement = this.control.xmlNode.firstChild;
  
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

XFormControlInstance.prototype.addInstantiatedLabel = function(label) {
};

XFormControlInstance.prototype.activate = function() {
  for (var i = this.innerControlInstances.length - 1; i >= 0; --i) {
    for (var j = this.innerControlInstances[i].length - 1; j >= 0; --j) {
      this.innerControlInstances[i][j].activate();
    }
  }
};

XFormControlInstance.prototype.deactivate = function() {
  for (var i = this.innerControlInstances.length - 1; i >= 0; --i) {
    for (var j = this.innerControlInstances[i].length - 1; j >= 0; --j) {
      this.innerControlInstances[i][j].deactivate();
    }
  }
};

XFormControlInstance.prototype.addLabel = function(htmlElement, label) {
  if (!label) {
    if (!this.control.label) {
      return htmlElement;
    }
    
    label = this.control.label;
  }
  
  var table = document.createElement("table");
  var tbody = document.createElement("tbody");
  var tr    = document.createElement("tr");
  var td    = document.createElement("td");
  
  table.appendChild(tbody);
  tbody.appendChild(tr);
  tr   .appendChild(td);
  td   .appendChild(label.htmlNode);
  td   .appendChild(document.createTextNode(" "));
  td   .appendChild(htmlElement);
  
  // Set the label's @for attribute to point to the HTML element.
  if (!htmlElement.id) {
    htmlElement.id = uniqueId();
  }
  
  label.labelElement.setAttribute("for", htmlElement.id);
  
  table.cellSpacing    = 0;
  table.style.display  = "inline";
  table.style.margin   = "0";
  table.style.padding  = "0";

  return table;
};

XFormControlInstance.prototype.postInstantiate = function() {
};

XFormControlInstance.prototype.setProperty = function(property, value) {
  if (typeof(classNames[property]) != "undefined") {
    var falseClass = classNames[property][0];
    var trueClass  = classNames[property][1];
    
    this.htmlNode.className  = this.htmlNode.className.replace(new RegExp("\\b" + falseClass + "\\b", "g"), "");
    this.htmlNode.className  = this.htmlNode.className.replace(new RegExp("\\b" + trueClass  + "\\b", "g"), "");
    
    this.htmlNode.className += " " + (value ? trueClass : falseClass);
  }
  
  /* switch (property) {
    case "text":       this.setValue     (value); break;
    case "readOnly":   this.setReadOnly  (value); break;
    case "required":   this.setRequired  (value); break;
    case "relevant":   this.setRelevant  (value); break;
    case "constraint": this.setConstraint(value); break;
    
    default:
      assert(false, "bad property: " + property);
  } */
  
  if(property == "text") {
    this.setValue(value);
  }
  else {
    if(property == "readOnly") {
      this.setReadOnly(value);
    }
    else {
      if(property == "required") {
        this.setRequired(value);
      }
      else {
        if(property == "relevant") {
          this.setRelevant(value);
        }
        else {
          if(property == "constraint") {
            this.setConstraint(value);
          }
          else {
            assert(false, "bad property: " + property);
          }
        }
      }
    }
  }
  
  this.touchProperty(property, value);
};

// Called to indicate that the specified property for this control has changed.
//
// Parameters:
//     property: The property name.
//     value:    The new value for the property.
XFormControlInstance.prototype.touchProperty = function(property, value) {
  var propListeners = this.listeners[property].length;
  for (var i = 0; i < propListeners; i++) {
    xform.waitingListeners.push([this.listeners[property][i], this, property, value]);
  }
};

// Adds a listener that is notified whenever the specified property of this
// control changes.
//
// Parameters:
//     property: The property to monitor.
//     listener: A function to call when the property value changes.
XFormControlInstance.prototype.addListener = function(property, listener) {
  this.listeners[property].push(listener);
};

// Gets the string value of the control.
XFormControlInstance.prototype.getValue = function() {
  throw new XFormException(this.xmlNode, this + " control is write-only.");
};

// Sets the string value of the control.
XFormControlInstance.prototype.setValue = function(value) {
};

// Should be called whenever the control's value changes. Changes the value of
// the underlying instance data and recalculates/refreshes the model.
//
// Parameters:
//     element:   The control's UI element. If the control has multiple UI
//                elements, valueHasChanged should be called for each one.
//     eventName: The name of the event to handle.
XFormControlInstance.prototype.valueHasChanged = function() {
  var model  = this.binding.model;
  var vertex = model.graph.getVertex(this.binding.boundNodes[0], "text");
  
  vertex.setValue(this.getValue());
  
  if (!model.hasChanged()) {
    return;
  }
  
  clearStatus();
  
  XmlEvent.dispatch(model.htmlNode, "xforms-recalculate");
  XmlEvent.dispatch(model.htmlNode, "xforms-revalidate");
  XmlEvent.dispatch(this .htmlNode, "xforms-value-changed");
  XmlEvent.dispatch(model.htmlNode, "xforms-refresh");
};

// Adds event handlers to the specified element to call valueHasChanged whenever
// the specified event is triggered.
//
// Parameters:
//     element:    The control's UI element. If the control has multiple UI
//                 elements, addEventHandlers should be called for each one.
//     eventNames: A list of event names to create listeners for.
XFormControlInstance.prototype.valueChangedOn = function(element, eventNames) {
  if (this.binding == null) {
    return;
  }
  
  var events = eventNames.length;
  for (var i = 0; i < events; i++) {
    new EventListener(
      element, eventNames[i], null,
      
      functionCall(setTimeout, methodCall(this, "valueHasChanged"), 1)
    );
  }
};

// Adds event handlers to the specified element to issue a DOMFocusIn/Out event
// whenever the specified HTML element gains/loses focus.
//
// Parameters:
//     element: The control's UI element, such as an <input/> or <select/>
//              element. If the control has multiple UI elements, this function
//              should be called for each one.
XFormControlInstance.prototype.watchForFocusChange = function(element) {
  new EventListener(element, "focus", null, functionCall(XmlEvent.dispatch, this.htmlNode, "DOMFocusIn"));
  new EventListener(element, "blur",  null, functionCall(XmlEvent.dispatch, this.htmlNode, "DOMFocusOut"));
};

// Adds an event handler to the specified element to issue a DOMActivate event
// when the user presses enter.
//
// Parameters:
//     element: The control's UI element, such as an <input/> or <select/>
//              element. If the control has multiple UI elements, this function
//              should be called for each one.
XFormControlInstance.prototype.activateOnEnter = function(element) {
  var self = this;
  
  new EventListener(element, "keypress", null,
    function(event) {
      if (event.keyCode == 13) {
        XmlEvent.dispatch(self.htmlNode, "DOMActivate");
      }
    }
  );
};


// Sets the read-only status of the control: if true, the control is made
// read-only; if false, the control is made read-write.
XFormControlInstance.prototype.setReadOnly = function(isReadOnly) {
};

// Sets the relevance of the control: if true, the control is enabled; if false,
// the control is disabled.
XFormControlInstance.prototype.setRelevant = function(isEnabled) {
};

// Sets the "requiredness" of the control: if true, a value is required; if
// false, a value is optional.
XFormControlInstance.prototype.setRequired = function(isRequired) {
};

// Sets the validity of the control: if true, the control is valid; if false,
// the control is invalid.
XFormControlInstance.prototype.setConstraint = function(isValid) {
};


XmlEvent.define("DOMActivate",          "Events", true,  true);
XmlEvent.define("DOMFocusIn",           "Events", true,  false);
XmlEvent.define("DOMFocusOut",          "Events", true,  false);
XmlEvent.define("xforms-select",        "Events", true,  false);
XmlEvent.define("xforms-deselect",      "Events", true,  false);
XmlEvent.define("xforms-value-changed", "Events", true,  false);

XmlEvent.define("xforms-valid",         "Events", true,  false);
XmlEvent.define("xforms-invalid",       "Events", true,  false);
XmlEvent.define("xforms-enabled",       "Events", true,  false);
XmlEvent.define("xforms-disabled",      "Events", true,  false);
XmlEvent.define("xforms-optional",      "Events", true,  false);
XmlEvent.define("xforms-required",      "Events", true,  false);
XmlEvent.define("xforms-readonly",      "Events", true,  false);
XmlEvent.define("xforms-readwrite",     "Events", true,  false);