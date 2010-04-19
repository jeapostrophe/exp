// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new XForms repeat control.
//
// Parameters:
//     element:       The element from which the repeat control was created.
//     bind:          The repeat's bind.
//     label:         The repeat's label, or null if it has none.
//     innerControls: The controls immediately enclosed by the repeat.
//     number:        The initial number of repeat items to display, or null if
//                    unspecified.
function XFormRepeatControl(element, bind, innerControls, number) {
  assert(bind          != null, "repeat: bind is null");
  assert(innerControls != null, "repeat: innerControls is null");
  
  XFormControl.call(this, element, bind, innerControls);
  
  this.number = number;
  this.index  = 0;
};

XFormRepeatControl.inherits(XFormControl);


XFormParser.prototype.parseRepeatControl = function(element) {
  var bind          = this.getBindFor   (element);
  var innerControls = this.parseControls(element);
  
  return new XFormRepeatControl(element, bind, innerControls, null);
};


XFormRepeatControl.prototype.createInstance = function(binding, htmlNode, outerBinding) {
  return new XFormRepeatControlInstance(this, binding, htmlNode, outerBinding);
};

function XFormRepeatControlInstance(control, binding, htmlNode, outerBinding) {
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding);
  
  this.container = this.htmlNode;
};

XFormRepeatControlInstance.inherits(XFormControlInstance);

XFormRepeatControlInstance.prototype.addInstantiatedLabel = function(label) {
  this.control.label = label;
};

XFormRepeatControlInstance.prototype.postInstantiate = function() {
  var childLength    = this.htmlNode.childNodes.length;
  var i              = 0;
  var nodesPerRepeat = childLength /
                       this.binding.boundNodes.length;
                       
  for (var child = this.htmlNode.firstChild; child != null; child = child.nextSibling) {
    new EventListener(child, "DOMFocusIn", "default",
      methodCall(this, "setIndex", Math.floor(i / nodesPerRepeat))
    );
    
    ++i;
  }
};

XFormRepeatControlInstance.prototype.setIndex = function(index) {
  if (index < 0)                               { index = 0; }
  if (index >= this.binding.boundNodes.length) { index = this.binding.boundNodes.length - 1; }
  
  if (this.control.activeInstance != null) {
    for (var node = this.control.activeInstance.htmlNode.firstChild; node != null; node = node.nextSibling) {
      
      if (typeof(node.className) != "undefined") {
        node.className = node.className.replace(/\bxforms-repeat-index\b/g, "");
      }
    }
  }

  var nodesPerRepeat = this.htmlNode.childNodes.length /
                       this.binding .boundNodes.length;
                       
  for (var i = 0; i < nodesPerRepeat; ++i) {
    var node = this.htmlNode.childNodes.item(index * nodesPerRepeat + i);
    
    if (typeof(node.className) != "undefined") {
      node.className += " xforms-repeat-index";
    }
  }

  this.control.index          = index;
  this.control.activeInstance = this;
  
  var innerInstances  = this.innerControlInstances;
  var instancesLength = innerInstances.length;
  for (var i = 0; i < instancesLength; i++) {
    var innerInnerInstances  = innerInstances[i];
    var innerInstancesLength = innerInnerInstances.length;
    for (var j = 0; j < innerInstancesLength; j++) {
      var innerControlInstance = innerInnerInstances[j];
      
      if (i == index) {
        innerControlInstance.activate();
      }
      else {
        innerControlInstance.deactivate();
      }
    }
  }
  
  status("Index changed to " + (index + 1) + ".");
};

XFormRepeatControlInstance.prototype.activate = function() {
  this.setIndex(this.control.index);
};

XFormRepeatControlInstance.prototype.setRelevant = function(isEnabled) {
};
  
XFormRepeatControl        .prototype.toString =
XFormRepeatControlInstance.prototype.toString = function() {
  return "repeat";
};