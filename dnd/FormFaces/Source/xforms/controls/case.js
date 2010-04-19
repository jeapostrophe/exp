// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new case control.
//
// Parameters:
//     element: The element from which the case control was created.
//     bind:    The control's bind.
function XFormCaseControl(element, bind, selected, innerControls) {
  XFormControl.call(this, element, bind, innerControls);
  
  this.selected = selected;
};

XFormCaseControl.inherits(XFormControl);

XFormCaseControl.prototype.toggle = function() {
  var cases  = this.switchControl.cases.length;
  
  for (var i = 0; i < cases; i++) {
    var caseControl = this.switchControl.cases[i];
    
    caseControl.instance.htmlNode.style.display = "none";
    XmlEvent.dispatch(caseControl.instance.htmlNode, "xforms-deselect");
  }
  
  this.instance.htmlNode.style.display = "";
  
  XmlEvent.dispatch(this.instance.htmlNode, "xforms-select");
};


XFormParser.prototype.parseCaseControl = function(element) {
  return new XFormCaseControl(
    element,

    this.getBindFor       (element),
    this.parseCaseSelected(element),
    this.parseControls    (element)
  );
};

XFormParser.prototype.parseCaseSelected = function(element) {
  return this.booleanValue(element, "selected", "false");
};


XFormCaseControl.prototype.createInstance = function(binding, htmlNode, outerBinding, position) {
  return this.instance = new XFormCaseControlInstance(this, binding, htmlNode, outerBinding, position);
};

function XFormCaseControlInstance(control, binding, htmlNode, outerBinding, position) {
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding, position);

  this.container  = document.createElement("span");
  this.isSelected = false;
  
  this.htmlNode.style.display = (this.control.selected) ? "" : "none";
  
  var labelElement = this.getLabelElement();
  
  if (labelElement == null) {
    this.htmlNode.appendChild(this.addLabel(this.container));
  }
};

XFormCaseControlInstance.inherits(XFormControlInstance);

XFormCaseControlInstance.prototype.addInstantiatedLabel = function(label) {
  this.control.label = label;
  this.htmlNode.appendChild(this.addLabel(this.container));
};

XFormCaseControl        .prototype.toString =
XFormCaseControlInstance.prototype.toString = function() {
  return "case";
};