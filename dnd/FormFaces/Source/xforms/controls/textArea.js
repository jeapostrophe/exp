// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new text area control.
//
// Parameters:
//     element: The element from which the text area was created.
//     bind:    The control's bind.
//     label:   The control's label.
function XFormTextAreaControl(element, bind, innerControls, incremental) {
  assert(bind  != null, "textarea: bind is null");
  assert(innerControls != null, "innerControls is null");
  
  var labelControl = null;
  var len = innerControls.length;
  for (var i = 0; i < len; i++) {
    if (innerControls[i] != null && innerControls[i] == "label") {
      labelControl = innerControls[i];
    }
  }
  
  assert(labelControl != null, "textarea: label is null");
  
  XFormControl.call(this, element, bind, innerControls);
  
  this.incremental = incremental;
};

XFormTextAreaControl.inherits(XFormControl);


XFormParser.prototype.parseTextAreaControl = function(element) {
  return new XFormTextAreaControl(
    element, 
    
    this.getBindFor      (element), 
    this.parseControls   (element),
    this.parseIncremental(element, false)
  );
};



XFormTextAreaControl.prototype.createInstance = function(binding, htmlNode, outerBinding) {
  return new XFormTextAreaControlInstance(this, binding, htmlNode, outerBinding);
};

function XFormTextAreaControlInstance(control, binding, htmlNode, outerBinding) {
  assert(binding != null, "binding is null");
  
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding);
  
  this.textArea = document.createElement("textarea");
  
  this.valueChangedOn(this.textArea,
    this.control.incremental
      ? ["keypress", "keydown", "click", "mousedown", "change"]
      : ["change"]
  );
  
  this.watchForFocusChange(this.textArea);
};

XFormTextAreaControlInstance.inherits(XFormControlInstance);

XFormTextAreaControlInstance.prototype.addInstantiatedLabel = function(label) {
  this.control.label = label;
  this.htmlNode.appendChild(this.addLabel(this.textArea));
};

XFormTextAreaControlInstance.prototype.getValue = function() {
  return this.textArea.value;
};

XFormTextAreaControlInstance.prototype.setValue = function(value) {
  if (this.textArea.value != value) {
      this.textArea.value  = value;
  }
};

XFormTextAreaControlInstance.prototype.setReadOnly = function(isReadOnly) {
  this.textArea.readOnly = isReadOnly;
};


XFormTextAreaControl        .prototype.toString =
XFormTextAreaControlInstance.prototype.toString = function() {
  return "textarea";
};