// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new load action.
//
// Parameters:
//     element:   The element from which this action was created.
//     resource:  The resource URI to load.
//     newWindow: Open the resource in a new window?
//     bind:      An optional bind.
function XFormLoadAction(element, resource, newWindow, bind) {
  XFormAction.call(this, element);

  this.resource  = resource;
  this.newWindow = newWindow;
  this.bind      = bind;
};

XFormLoadAction.inherits(XFormAction);


XFormParser.prototype.parseLoadAction = function(element) {
  return new XFormLoadAction(
    element,
  
    this.parseLoadActionResource(element),
    this.parseLoadActionShow    (element) == "new",
    this.getBindFor             (element)
  );
};

XFormParser.prototype.parseLoadActionResource = function(element) {
  return this.stringValue(element, "resource");
};

XFormParser.prototype.parseLoadActionShow = function(element) {
  return this.stringValue(element, "show", "replace");
};


XFormLoadAction.prototype.activate = function() {
  if (this.newWindow) {
    window.open(this.resource);
  }
  else {
    window.location = this.resource;
  }
};

XFormLoadAction.prototype.toString = function() {
  return "load";
};