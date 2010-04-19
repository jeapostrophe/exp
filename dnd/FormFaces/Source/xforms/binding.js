// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new bind, either from a <bind/> element or from a element bound
// with a @ref or @nodeset attribute.
//
// Parameters:
//     element:    The element from which this bind was created.
//
//     type:       The bind type, either "ref" or "nodeset".
//     xpath:      The binding expression from the @ref or @nodeset attribute.
//
//     properties: An associative array of model item property XPath
//                 expressions. The expected properties are readOnly, required,
//                 relevant, calculate, and constraint.
function XFormBind(element, type, xpath, properties) {
  XFormObject.call(this, element, properties != null);

  this.type       = type;
  this.xpath      = xpath;
  this.properties = (properties != null) ? properties : { };

  // If "calculate" is given then "readonly" defaults to "true()".
  if (this.properties.calculate && !this.properties.readOnly) {
    this.properties.readOnly = new XPath("true()");
  }

  this.outerBind  = null;
  this.index      = null;
  this.innerBinds = [];

  this.defaultBinding = null;
};

XFormBind.inherits(XFormObject);

XFormBind.prototype.setModel = function(model) {
  this.model       = model;
  var innerBindLen = this.innerBinds.length;

  //for (var i in this.innerBinds) {
  for (var i = 0; i < innerBindLen; ++i) {
    this.innerBinds[i].setModel(model);
  }
};

XFormBind.prototype.toString = function() {
  var string = "<bind " + this.type + '="' + this.xpath + '"';

  for (var property in this.properties) {
    if (this.properties[property] != null) {
      string += " " + property + '="' + this.properties[property] + '"';
    }
  }

  if (this.innerBinds.length == 0) {
    string += "/>";
  }
  else {
    string += ">\n";

    var innerBindLen = this.innerBinds.length;
    //for (var i in this.innerBinds) {
    for (var i = 0; i < innerBindLen; ++i) {
      string += "  " + this.innerBinds[i].toString().replace(/\n/g, "\n  ") + "\n";
    }

    string += "</bind>";
  }

  return string;
};


XFormParser.prototype.parseBinds = function(element) {
  var binds        = [];

  for (var child = element.firstChild; child != null; child = child.nextSibling) {
    if (child.nodeType == 1 && child.nodeName.replace(/^.*:/, "") == "bind" && child.namespaceURI == XmlNamespaces.XFORMS) {
      binds.push(this.parseBind(child));
    }
  }

  return binds;
};

XFormParser.prototype.parseBind = function(element) {
  var bind = new XFormBind(
    element,

    "nodeset",
    this.xpathValue(element, "nodeset"),

    // Model item properties.
    { readOnly:   this.xpathValue(element, "readonly",   null),
      required:   this.xpathValue(element, "required",   null),
      relevant:   this.xpathValue(element, "relevant",   null),
      calculate:  this.xpathValue(element, "calculate",  null),
      constraint: this.xpathValue(element, "constraint", null)
    }
  );

  var outerBind  = bind;
  var innerBinds = this.parseBinds(element);

  var innerBindLen = innerBinds.length;
  //for (var i in innerBinds) {
  for (var i = 0; i < innerBindLen; ++i) {
    var innerBind = innerBinds[i];

    innerBind.outerBind = outerBind;
    innerBind.index     = i;

    outerBind.innerBinds.push(innerBind);
  }

  return bind;
};


XFormParser.prototype.parseBoundElements = function(element, contextModel, outerBind) {
  // Get all bound elements, excluding <bind/> and <submission/> elements, which
  // have already been parsed.
  var boundElements = new NodeSet();
  var binds         = [];

  locateBoundElements(boundElements, element);

  // If there are bound elements then there must be a model.
  if (boundElements.length > 0 && xform.models.length == 0) {
    throw new XFormException(element, "Document does not contain a model.");
  }

  for (var i = boundElements.length - 1; i >= 0; --i) {
    var innerBind = this.parseBoundElement(boundElements[i], contextModel, outerBind);

    // If this element has a @bind attribute, check that the corresponding <bind/>'s
    // outer <bind/> is the same as the bind for the outer bound element. If that
    // makes any sense.
    var bindXmlElement = innerBind.xmlElement;
    if(bindXmlElement.nodeName.replace(/^.*:/, "") == "bind" && bindXmlElement.namespaceURI == XmlNamespaces.XFORMS) {
      if (innerBind.outerBind != outerBind) {
        throw new XFormException(boundElements[i].attributes.getNamedItem("bind"),
          "<" + element.tagName + "/>'s binding is improperly nested."
        );
      }
    }
    // The bind for the bound element was created from a @ref or @nodeset attribute,
    // so add it to the binds list and set its outerBind.
    else {
      binds.push(innerBind);
      
      if (outerBind != null) {
        innerBind.outerBind = outerBind;
        innerBind.index     = outerBind.innerBinds.length;

        outerBind.innerBinds.push(innerBind);
      }
    }
  }

  return binds;


  // Locates any bound elements underneath the specified element and adds them to
  // the boundElements node-set.
  //
  // Parameters:
  //     boundElements: The node-set to add the bound elements to.
  //     element:       The parent element under which to search for bound
  //                    elements.
  function locateBoundElements(boundElements, element) {
    for (var child = element.lastChild; child != null; child = child.previousSibling) {
      if(child.nodeType == 1) {
        if(child.getAttributeNode("bind") != null || child.getAttributeNode("nodeset") != null 
          || child.getAttributeNode("ref") != null) {
          var childName = child.nodeName.replace(/^.*:/, "");
          if((childName != "submission" && childName != "bind") && child.namespaceURI == XmlNamespaces.XFORMS) {
            boundElements.addUnique(child);
          }
        }
        else {
          var atts  = child.attributes;
          var bound = false;

          for (var i = atts.length - 1; i > -1; i--) {
            var att = atts.item(i);
            if(att != null && att.namespaceURI == XmlNamespaces.XFORMS) {
              var attName = att.nodeName.replace(/^.*:/, "");
              if(attName == "repeat-bind" || attName == "repeat-nodeset") {
                bound = true;
                break;
              }
            }
          }
          if (bound) {
            boundElements.addUnique(child);
          }
          else {
            locateBoundElements(boundElements, child);
          }
        }
      }
    }
  };
};

XFormParser.prototype.parseBoundElement = function(element, contextModel, outerBind) {
  var bindAttribute = element.getAttributeNode("bind");

  if(bindAttribute == null && element.namespaceURI != XmlNamespaces.XFORMS) {
    var atts = element.attributes;
    for(var i = atts.length - 1; i > -1; i--) {
      var att = atts.item(i);
      if (att != null && att.namespaceURI == XmlNamespaces.XFORMS && att.nodeName.replace(/^.*:/, "") == "repeat-bind") {
        bindAttribute = att;
        break;
      }
    }
  }

  // Find the bind with the specified ID.
  if (bindAttribute != null) {
    var bind = xform.getObjectById(bindAttribute);

    if (contextModel != null && bind.model != contextModel) {
      throw new XFormException(bindAttribute,
        "<" + element.tagName + "/> is bound to a different model than the immediately enclosing element."
      );
    }

    this.parseBoundElements(element, bind.model, bind);

    return bind;
  }
  // Create a bind from the @nodeset or @ref attribute.
  else {
    var nodesetAttribute = element.getAttributeNode("nodeset");
    var refAttribute = element.getAttributeNode("ref");
    var modelAttribute = element.getAttributeNode("model");

    if(nodesetAttribute == null && refAttribute == null) {
      var atts = element.attributes;
      for(var i = atts.length - 1; i > -1; i--) {
        var att = atts.item(i);
        if (att != null && att.namespaceURI == XmlNamespaces.XFORMS && att.nodeName.replace(/^.*:/, "") == "repeat-nodeset") {
          nodesetAttribute = att;
          break;
        }
      }
    }

    assert(nodesetAttribute != null || refAttribute != null, "missing @nodeset or @ref");

    var type  = (nodesetAttribute != null) ? "nodeset" : "ref";
    var xpath = new XPath((nodesetAttribute != null) ? nodesetAttribute.value : refAttribute.value, element);

    var model = (contextModel != null ? contextModel : xform.models[0]);

    // Get the context model from the @model attribute.
    if (modelAttribute != null) {
      model = xform.getObjectById(modelAttribute, XFormModel);

      if (contextModel != null && model != contextModel) {
        throw new XFormException(modelAttribute,
          "<" + element.tagName + "/> is bound to a different model than the immediately enclosing element."
        );
      }
    }

    var bind   = new XFormBind(element, type, xpath, null);
    bind.model = model;

    if (contextModel == null) {
      bind .index = model.binds.length;

      bind .setModel  (model);
      model.binds.push(bind);
    }

    this.parseBoundElements(element, model, bind);

    return bind;
  }
};

// Gets the XFormBind that was created for the specified element.
//
// Parameters:
//     boundElement: An element with binding attributes.
//
// Return value:
//     The XFormBind for the element, or null if the element is unbound.
XFormParser.prototype.getBindFor = function(boundElement, debug) {
  if (boundElement.attributes.getNamedItem("bind") != null) {
    var bind = xform.getObjectById(boundElement.attributes.getNamedItem("bind"));

    assert(instanceOf(bind, XFormBind), "bind is not an XFormBind");

    return bind;
  }

  var models   = xform.models;
  var modelLen = models.length;
  for (var i = 0; i < modelLen; ++i) {
    var bind  = getBindFor(boundElement, models[i].binds);

    if (bind != null) {
      return bind;
    }
  }

  return null;


  // Recursive function to search for the bind for the specified element in the
  // given list of binds and their inner binds.
  function getBindFor(boundElement, binds) {
    for (var i = binds.length - 1; i >= 0; --i) {
      var bind = binds[i];

      if (bind.xmlElement == boundElement) {
        return bind;
      }

      var innerBind = getBindFor(boundElement, bind.innerBinds);

      if (innerBind != null) {
        return innerBind;
      }
    }

    return null;
  };
};


XFormBind.prototype.reset = function() {
  this.defaultBinding = null;
  
  for (var i = this.innerBinds.length - 1; i >= 0; --i) {
    this.innerBinds[i].reset();
  }
};


XFormBind.nonRelevantNode = xmlNewDocument().createElement("non-relevant");

XFormBind.prototype.createBinding = function(context) {
  var boundNodes    = this.xpath.evaluate(context);
  var innerBindings = [];

  if (boundNodes.length == 0) {
    boundNodes = new NodeSet([XFormBind.nonRelevantNode]);
  }

  // If this is a "ref" binding, only use the first node.
  if (this.type == "ref" && boundNodes.length > 0) {
    boundNodes = new NodeSet([boundNodes[0]]);
  }

  var boundNodeLen  = boundNodes.length;
  for (var i = 0; i < boundNodeLen; ++i) {
    innerBindings[i] = [];

    var innerBinds   = this.innerBinds;
    var innerBindLen = innerBinds.length;
    for (var j = 0; j < innerBindLen; ++j) {
      innerBindings[i][j] = innerBinds[j].createBinding(new XPathContext(boundNodes[i], i + 1, boundNodeLen));
    }
  }

  var binding = new XFormBinding(this, context, boundNodes, innerBindings);

  if (this.defaultBinding == null) {
    this.defaultBinding = binding;
  }

  return binding;
};


// Creates a new binding, which is a joining of bound nodes, their model item
// properties, and the bound controls.
function XFormBinding(bindOrModel, context, boundNodes, innerBindings) {
  if (instanceOf(bindOrModel, XFormBind)) {
    this.bind  = bindOrModel;
    this.model = bindOrModel.model;

    assert(this.model != null, "this.model is null");
  }
  else {
    assert(instanceOf(bindOrModel, XFormModel), "bindOrModel is not an XFormModel");

    this.bind  = null;
    this.model = bindOrModel;
  }

  this.context       = context;
  this.boundNodes    = boundNodes;

  this.outerBinding  = null;
  this.innerBindings = innerBindings;

  for (var i = this.innerBindings.length - 1; i >= 0; --i) {
    for (var j = this.innerBindings[i].length - 1; j >= 0; --j) {
      this.innerBindings[i][j].outerBinding = this;
    }
  }

  this.controls = [];
};

// Adds the dependency information for this binding to the specified dependency
// graph, creating vertices for each model item property of each bound node.
//
// Parameters:
//     graph: A dependency graph.
XFormBinding.prototype.setupGraph = function(graph) {
  var boundNodeList   = this.boundNodes;
  var boundNodeLen = boundNodeList.length;
  for (var i = 0; i < boundNodeLen; ++i) {
    var boundNode    = boundNodeList[i];
    var boundContext = new XPathContext(boundNode, i + 1, boundNodeLen);
    var boundVertex  = graph.addVertex(boundNode, "text");

    for (var property in this.bind.properties) {
      if (!this.bind.properties[property]) {
        continue;
      }

      var xpath         = this.bind.properties[property];
      var references    = xpath.referencedNodes(boundContext);
      var vertex        = graph.addVertex(boundNode, property, boundContext, xpath);
      var referencesLen = references.length;

      for (var j = 0; j < referencesLen; ++j) {
        vertex.dependsOn(graph.addVertex(references[j], "text"));
      }

      if (property == "calculate") {
        boundVertex.dependsOn(vertex);
      }
    }
  }

  if (this.outerBinding == null) {
    //XForm.alertTime("Setup graph in %t seconds.");
  }

  var bindingsLen = this.innerBindings.length;
  for (var i = 0; i < bindingsLen; ++i) {
    var innerBindingsLen = this.innerBindings[i].length;
    for (var j = 0; j < innerBindingsLen; ++j) {
      this.innerBindings[i][j].setupGraph(graph);
    }
  }

  //if (this.outerBinding == null) {
    //XForm.alertTime("Setup graph for inner bindings in %t seconds.");
  //}
};

// Gets the nodes the binding is bound to, re-evaluating the binding XPath. The
// recommended way to get the bound node-set is to access the binding.boundNodes
// property. Call this function if that node-set is stale.
XFormBinding.prototype.getBoundNodes = function() {
  assert(this.context != null, "context is null");

  return this.bind.xpath.evaluate(this.context);
};

XFormBinding.prototype.toString = function() {
  return this.boundNodes.toString() + "\n\n" + this.bind.toString();
};