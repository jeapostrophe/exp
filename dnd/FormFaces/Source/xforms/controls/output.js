// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new XForms output control.
//
// Parameters:
//     element: The element from which the output control was created.
//     bind:    The control's bind, or an XPath expression if the <output/>
//              element had a @value attribute.
//     label:   The control's label, or null if it has none.
function XFormOutputControl(element, bind, innerControls) {
  if (instanceOf(bind, XFormBind)) {
    XFormControl.call(this, element, bind, innerControls);
  }
  else {
    if (bind == null) {
      XFormControl.call(this, element, null, innerControls);
    }
    else {
      assert(instanceOf(bind, XPath), "bind is not an XPath");
      
      XFormControl.call(this, element, null, innerControls);
      
      this.value = bind;
    }
  }
};

XFormOutputControl.inherits(XFormControl);


XFormParser.prototype.parseOutputControl = function(element) {
  var bind          = this.getBindFor   (element);
  var innerControls = this.parseControls(element);
  
  if (bind != null)  {
    return new XFormOutputControl(element, bind, innerControls);
  }
  
  var value = this.xpathValue(element, "value", null);
  
  return new XFormOutputControl(element, value, innerControls);
};


XFormOutputControl.prototype.createInstance = function(binding, htmlNode, outerBinding) {
  return new XFormOutputControlInstance(this, binding, htmlNode, outerBinding);
};

function XFormOutputControlInstance(control, binding, htmlNode, outerBinding) {
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding);
  
  this.output = document.createElement("span");
  
  var labelElement = this.getLabelElement();
  
	if(labelElement == null) {
    this.htmlNode.appendChild(this.addLabel(this.output));
	}
};

XFormOutputControlInstance.inherits(XFormControlInstance);

XFormOutputControlInstance.prototype.addInstantiatedLabel = function(label) {
	this.control.label = label;
	this.htmlNode.appendChild(this.addLabel(this.output));
};

XFormOutputControlInstance.prototype.setValue = function(value) {
  while (this.output.hasChildNodes()) {
    this.output.removeChild(this.output.lastChild);
  }
  
  this.output.appendChild(document.createTextNode(value));
};

XFormOutputControl        .prototype.toString =
XFormOutputControlInstance.prototype.toString = function() {
  return "output";
};