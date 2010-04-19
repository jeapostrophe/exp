// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new input control.
//
// Parameters:
//     element: The element from which the input control was created.
//     bind:    The control's bind.
//     label:   The control's label.
function XFormInputControl(element, bind, innerControls, incremental) {
  assert(bind  != null, "input: bind is null");
  assert(innerControls != null, "innerControls is null");
  
  var labelControl     = null;
  var numInnerControls = innerControls.length;
  
  for (var i = 0; i < numInnerControls; i++) {
    if (innerControls[i] != null && innerControls[i] == "label") {
      labelControl = innerControls[i];
    }
  }
  
  assert(labelControl != null, "input: label is null");
  
  XFormControl.call(this, element, bind, innerControls);
  
  this.incremental = incremental;
};

XFormInputControl.inherits(XFormControl);


XFormParser.prototype.parseInputControl = function(element) {
  return new XFormInputControl(
    element,
    
    this.getBindFor      (element),
    this.parseControls   (element),
    this.parseIncremental(element, false)
  );
};


XFormInputControl.prototype.createInstance = function(binding, htmlNode, outerBinding) {
  return new XFormInputControlInstance(this, binding, htmlNode, outerBinding);
};

function XFormInputControlInstance(control, binding, htmlNode, outerBinding) {
  assert(binding != null, "binding is null");
  
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding);
  
  this.inControl      = document.createElement("input");
  this.inControl.type = "text";
  
  this.valueChangedOn(this.inControl,
    this.control.incremental
      ? ["keypress", "keydown", "click", "mousedown", "change"]
      : ["change"]
  );
  
  this.watchForFocusChange(this.inControl);
  this.activateOnEnter    (this.inControl);
};

XFormInputControlInstance.inherits(XFormControlInstance);

XFormInputControlInstance.prototype.addInstantiatedLabel = function(label) {
	this.control.label = label;
	this.htmlNode.appendChild(this.addLabel(this.inControl));
};

XFormInputControlInstance.prototype.getValue = function() {
  return this.inControl.value;
};

XFormInputControlInstance.prototype.setValue = function(value) {
  if (this.inControl.value != value) {
      this.inControl.value  = value;
  }
};

XFormInputControlInstance.prototype.setReadOnly = function(isReadOnly) {
  this.inControl.readOnly = isReadOnly;
};


XFormInputControl        .prototype.toString =
XFormInputControlInstance.prototype.toString = function() {
  return "input";
};