// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new label.
//
// Parameters:
//     element:  The element from which the label was created.
//     bind:     The label's bind, or null if it is unbound.
//     children: Any controls inside of the label.
function XFormLabel(element, bind, children) {
  XFormControl.call(this, element, bind, children);
};

XFormLabel.inherits(XFormControl);


XFormParser.prototype.parseLabel = function(element) {
  var labelElement = this.getLabelElement(element);
  var parseElement = (labelElement == null) ? element : labelElement;

  if (parseElement == null) {
    return null;
  }

  var bind     = this.getBindFor   (parseElement);
  var children = this.parseUiInline(parseElement);

  return new XFormLabel(parseElement, bind, children);
};


XFormLabel.prototype.createInstance = function(binding, htmlNode, outerBinding, position) {
  return new XFormLabelInstance(this, binding, htmlNode, outerBinding, position);
};

function XFormLabelInstance(control, binding, htmlNode, outerBinding, position) {
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding, position);

  this.labelElement = document.createElement("label");
  this.container    = this.labelElement;

  this.htmlNode.appendChild(this.labelElement);
  this.htmlNode.className = "xforms-label";
};

XFormLabelInstance.inherits(XFormControlInstance);

XFormLabelInstance.prototype.postInstantiate = function() {
  var self           = this;
  var innerInstances = this.innerControlInstances[0].length;
  
  for (var i = 0; i < innerInstances; i++) {
    this.innerControlInstances[0][i].addListener("text", function() {
      self.touchProperty("text", self.getValue());
    });
  }

  // Notify parent control that the label has been instantiated.
  var parent   = this.enclosedBy;
  var ancestor = this.xmlElement.parentNode;
  
  while (ancestor != null && ancestor.namespaceURI != XmlNamespaces.XFORMS) {
    ancestor = ancestor.parentNode;
  }
  
  if (XForm.isXFormsElement(ancestor, ["item", "itemset"])) {
    return;
  }

  if (parent == null) {
    var parentControl = xform.getObjectByNode(ancestor);
    parent = parentControl.activeInstance;
  }

  parent.addInstantiatedLabel(this);
};

XFormLabelInstance.prototype.getValue = function() {
  return XPathFunction.stringValueOf(this.labelElement);
};

XFormLabelInstance.prototype.setValue = function(value) {
  // Remove the current contents of the label and replace them with a new text
  // node.
  while (this.labelElement.hasChildNodes()) {
    this.labelElement.removeChild(this.labelElement.firstChild);
  }

  this.labelElement.appendChild(document.createTextNode(value));
};


XFormLabel        .prototype.toString =
XFormLabelInstance.prototype.toString = function() {
  return "label";
};