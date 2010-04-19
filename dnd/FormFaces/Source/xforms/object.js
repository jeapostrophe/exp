// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new XForm object, an object that stores the information parsed from
// a node in the XForms document.
//
// Parameters:
//     xmlNode:     The element or other node from which the object was created.
//
//     isCanonical: Is this the canonical object for the node? For example, an
//                  <input/> element might have a corresponding
//                  XFormInputControl and XFormBind object. The
//                  XFormInputControl is the canonical object.
//
//                  TODO: Find a better word to describe this concept.
function XFormObject(xmlNode, isCanonical) {
  // If being called by inherits() method, don't do anything.
  if (arguments.length == 0) {
    return;
  }
  
  assert(xmlNode != null, "xmlNode is null");
  
  this.xmlNode    = xmlNode;
  this.xmlElement = (xmlNode.nodeType == 1) ? xmlNode : null;
  this.htmlNode   = null;
  this.id         = null;
  
  if (isCanonical) {
    xform.objectsByNode.push([xmlNode, this]);
    
    var id = xmlNode.getAttribute("id");

    if (id != null) {
      xform.objectsById[this.id = id] = this;
    }
  }
};

XFormObject.prototype.render = function() {
  this.htmlNode           = document.createElement("span");
  this.htmlNode.className = "xforms-" + this.xmlNode.nodeName.replace(/^.*:/, "");
  
  if (this.id != null) {
    this.htmlNode.id = this.id;
  }
  
  xform.nodeHasBeenRendered(this.xmlNode, this.htmlNode);
  
  this.postRender();
  
  return this.htmlNode;
};

// Called after an object is rendered. Can be overridden to attach event
// handlers and the like to the rendered node.
XFormObject.prototype.postRender = function() {
};


// Finds the object with the specified @id.
//
// Parameters:
//     idref:       The ID of the object to find. This can be either a value or
//                  a DOM attribute.
//     Constructor: If given, the object must be of this type. (Optional.)
//
// Return value:
//     The object with the specified @id.
//
// Exceptions:
//     
XForm.prototype.getObjectById = function(idref, Constructor) {
  assert(idref != null, "idref is null");
  
  if (typeof(idref.value) == "undefined") {
    var object = this.objectsById[idref];
  
    if (!object || Constructor != null && !instanceOf(object, Constructor)) {
      throw new XFormException(null, "Invalid element ID (" + idref + ").");
    }
  }
  else {
    var object = this.objectsById[idref.value];
  
    if (!object || Constructor != null && !instanceOf(object, Constructor)) {
      throw new XFormException(idref,
        "@" + idref.name + " attribute has an invalid element ID (" + idref.value + ")."
      );
    }
  }
  
  return object;
};

XForm.prototype.getObjectByNode = function(xmlNode) {
  var objLen = this.objectsByNode.length;
  
  for (var i = 0; i < objLen; ++i) {
    if (this.objectsByNode[i][0] == xmlNode) {
      return this.objectsByNode[i][1];
    }
  }
  
  assert(false, "No object for node:\n" + xmlSerialize(xmlNode));
};