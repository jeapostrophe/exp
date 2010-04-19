// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


XPath.LAST_FUNCTION = new XPathFunction(
  function(context) {
    return context.size;
  },
  
  XPathFunction.Context.REQUIRED
);


XPath.POSITION_FUNCTION = new XPathFunction(
  function(context) {
    return context.position;
  },

  XPathFunction.Context.REQUIRED
);


XPath.COUNT_FUNCTION = new XPathFunction(
  function(nodeSet) {
    return nodeSet.length;
  },
  
  XPathFunction.Context.NONE
);

XPath.CURRENT_FUNCTION = new XPathFunction(
  function(context) {
    return new NodeSet([context.currentNode]);
  },
  
  XPathFunction.Context.REQUIRED
);


XPath.ID_FUNCTION = new XPathFunction(
  function(context, object) {
    var result = new NodeSet();
    
    if (instanceOf(object, NodeSet)) {
      for (var i = object.length - 1; i >= 0; --i) {
        result.addAll(XPath.ID_FUNCTION.evaluate(context, object[i]));
      }
    }
    else if (context.node != null) {
      var ids = XPath.STRING_FUNCTION.evaluate(object).split(/\s+/);
      
      for (var i = ids.length - 1; i >= 0; --i) {
        result.add(context.node.ownerDocument.getElementById(ids[i]));
      }
    }
    
    return result;
  },
  
  XPathFunction.Context.REQUIRED
);


XPath.LOCAL_NAME_FUNCTION = new XPathFunction(
  function(nodeSet) {
    if (nodeSet.length == 0) {
      return "";
    }
    
    return nodeSet[0].nodeName.replace(/^.*:/, "");
  },
  
  XPathFunction.Context.NONE,
  XPathFunction.DefaultTo.CONTEXT_NODESET
);


XPath.NAMESPACE_URI_FUNCTION = new XPathFunction(
  function(nodeSet) {
    if (nodeSet.length == 0) {
      return "";
    }
    
    return xmlNamespaceURI(nodeSet[0]);
  },
  
  XPathFunction.Context.NONE,
  XPathFunction.DefaultTo.CONTEXT_NODESET
);


XPath.NAME_FUNCTION = new XPathFunction(
  function(nodeSet) {
    if (nodeSet.length == 0) {
      return "";
    }
    
    return nodeSet[0].nodeName;
  },

  XPathFunction.Context.NONE,
  XPathFunction.DefaultTo.CONTEXT_NODESET
);


XPath.STRING_FUNCTION = new XPathFunction(
  function(object) {
    assert(object != null, "object is null");
    
    switch (object.constructor) {
      case String:  return object;
      case Boolean: return object ? "true" : "false";
      case NodeSet: return object.length > 0 ? XPathFunction.stringValueOf(object[0]) : "";
      
      case Number:
        var string = object.toString();
        
        // Try to round the number a bit better if toString() returns something like
        // 102.91000000000001.
        if (string.match(/^(\d+\.\d*?)0{6,}\d$/)) {
          string = RegExp.$1;
        }
        else if (string.match(/^(\d+\.\d*?)(\d)9{6,}\d$/)) {
          string = RegExp.$1 + (+RegExp.$2 + 1);
        }
        
        return string;
    }
  },

  XPathFunction.Context.NONE,
  XPathFunction.DefaultTo.CONTEXT_NODESET
);


XPath.CONCAT_FUNCTION = new XPathFunction(
  function() {
    var string = "";
    var argLen = arguments.length;
    
    for (var i = 0; i < argLen; ++i) {
      string += XPath.STRING_FUNCTION.evaluate(arguments[i]);
    }
    
    return string;
  },
  
  XPathFunction.Context.NONE
);


XPath.STARTS_WITH_FUNCTION = new XPathFunction(
  function(string, prefix) {
    string = XPath.STRING_FUNCTION.evaluate(string);
    prefix = XPath.STRING_FUNCTION.evaluate(prefix);
    
    return string.indexOf(prefix) == 0;
  },
  
  XPathFunction.Context.NONE
);


XPath.CONTAINS_FUNCTION = new XPathFunction(
  function(string, substring) {
    string    = XPath.STRING_FUNCTION.evaluate(string);
    substring = XPath.STRING_FUNCTION.evaluate(substring);
    
    return string.indexOf(substring) != -1;
  },
  
  XPathFunction.Context.NONE
);


XPath.SUBSTRING_BEFORE_FUNCTION = new XPathFunction(
  function(string, substring) {
    string    = XPath.STRING_FUNCTION.evaluate(string);
    substring = XPath.STRING_FUNCTION.evaluate(substring);
    
    return string.substring(0, string.indexOf(substring));
  },
  
  XPathFunction.Context.NONE
);


XPath.SUBSTRING_AFTER_FUNCTION = new XPathFunction(
  function(string, substring) {
    string    = XPath.STRING_FUNCTION.evaluate(string);
    substring = XPath.STRING_FUNCTION.evaluate(substring);
    
    var index = string.substring(substring);
    
    if (index == -1) {
      return "";
    }
    
    return string.substring(index + substring.length);
  },
  
  XPathFunction.Context.NONE
);


XPath.SUBSTRING_FUNCTION = new XPathFunction(
  function(string, index, length) {
    string = XPath.STRING_FUNCTION.evaluate(string);
    index  = XPath.NUMBER_FUNCTION.evaluate(index);
    length = XPath.NUMBER_FUNCTION.evaluate(length);
    
    return string.substr(
      XPath.ROUND_FUNCTION.evaluate(index) - 1,
      XPath.ROUND_FUNCTION.evaluate(length)
    );
  },
  
  XPathFunction.Context.NONE
);


XPath.STRING_LENGTH_FUNCTION = new XPathFunction(
  function(string) {
    string = XPath.STRING_FUNCTION.evaluate(string);

    return string.length;
  },
  
  XPathFunction.Context.NONE,
  XPathFunction.DefaultTo.CONTEXT_STRING
);


XPath.NORMALIZE_SPACE_FUNCTION = new XPathFunction(
  function(string) {
    string = XPath.STRING_FUNCTION.evaluate(string);

    return string.replace(/^\s+|\s+$/g, "")
                 .replace(/\s+/,        " ");
  },
  
  XPathFunction.Context.NONE,
  XPathFunction.DefaultTo.CONTEXT_STRING
);


XPath.TRANSLATE_FUNCTION = new XPathFunction(
  function(string, from, to) {
    string = XPath.STRING_FUNCTION.evaluate(string);
    from   = XPath.STRING_FUNCTION.evaluate(from);
    to     = XPath.STRING_FUNCTION.evaluate(to);
    
    var result = "";
    var strLen = string.length;
    
    for (var i = 0; i < strLen; ++i) {
      var index = from.indexOf(string.charAt(i));
      
      if (index == -1) {
        result += string.charAt(i);
      }
      else {
        result += to.charAt(index);
      }
    }
  },
  
  XPathFunction.Context.NONE
);


XPath.BOOLEAN_FUNCTION = new XPathFunction(
  function(object) {
    switch (object.constructor) {
      case String:  return object != "";
      case Number:  return object != 0 && !isNaN(object);
      case Boolean: return object;
      case NodeSet: return object.length > 0;
    }
  },

  XPathFunction.Context.NONE
);


XPath.NOT_FUNCTION = new XPathFunction(
  function(condition) {
    condition = XPath.BOOLEAN_FUNCTION.evaluate(condition);
    
    return !condition;
  },
  
  XPathFunction.Context.NONE
);


XPath.TRUE_FUNCTION  = new XPathFunction(function() { return true;  });
XPath.FALSE_FUNCTION = new XPathFunction(function() { return false; });


XPath.LANG_FUNCTION = new XPathFunction(
  function(context, language) {
    language = XPath.STRING_FUNCTION.evaluate(language);
    
    // Find the nearest xml:lang attribute.
    for (var node = context.node; node != null; node = node.parentNode) {
      if (typeof(node.attributes) == "undefined") {
        continue;
      }
      
      var xmlLang = node.attributes.getNamedItemNS(XmlNamespaces.XML, "lang");
      
      if (xmlLang != null) {
        xmlLang  = xmlLang.value.toLowerCase();
        language = language     .toLowerCase();
        
        return xmlLang.indexOf(language) == 0
          && (language.length == xmlLang.length || language.charAt(xmlLang.length) == '-');
      }
    }
    
    // Didn't find an xml:lang attribute.
    return false;
  },
  
  XPathFunction.Context.REQUIRED
);


XPath.NUMBER_FUNCTION = new XPathFunction(
  function(object) {
    switch (object.constructor) {
      case String:  return object.match(/^\s*-?(\d+(\.\d+)?|\.\d+)*\s*$/) ? Number(object) : Number.NaN;
      case Number:  return object;
      case Boolean: return object ? 1 : 0;
      case NodeSet: return XPath.NUMBER_FUNCTION.evaluate(XPath.STRING_FUNCTION.evaluate(object));
    }
  },
  
  XPathFunction.Context.NONE,
  XPathFunction.DefaultTo.CONTEXT_NODESET
);


XPath.SUM_FUNCTION = new XPathFunction(
  function(nodeSet) {
    var sum    = 0;
    
    for (var i = nodeSet.length - 1; i >= 0; --i) {
      sum += XPath.NUMBER_FUNCTION.evaluate(XPathFunction.stringValueOf(nodeSet[i]));
    }
    
    return sum;
  },
  
  XPathFunction.Context.NONE
);


XPath.FLOOR_FUNCTION = new XPathFunction(
  function(number) {
    number = XPath.NUMBER_FUNCTION.evaluate(number);
    
    return Math.floor(number);
  },
  
  XPathFunction.Context.NONE
);


XPath.CEILING_FUNCTION = new XPathFunction(
  function(number) {
    number = XPath.NUMBER_FUNCTION.evaluate(number);

    return Math.ceil(number);
  },
  
  XPathFunction.Context.NONE
);


XPath.ROUND_FUNCTION = new XPathFunction(
  function(number) {
    number = XPath.NUMBER_FUNCTION.evaluate(number);

    return Math.round(number);
  },
  
  XPathFunction.Context.NONE
);



XPath.CORE_FUNCTIONS = new XPathFunctionMap();

XPath.CORE_FUNCTIONS.registerFunction(new QName("last"),             XPath.LAST_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("position"),         XPath.POSITION_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("count"),            XPath.COUNT_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("current"),          XPath.CURRENT_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("id"),               XPath.ID_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("local-name"),       XPath.LOCAL_NAME_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("namespace-uri"),    XPath.NAMESPACE_URI_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("name"),             XPath.NAME_FUNCTION);
                                                                    
XPath.CORE_FUNCTIONS.registerFunction(new QName("string"),           XPath.STRING_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("concat"),           XPath.CONCAT_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("starts-with"),      XPath.STARTS_WITH_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("contains"),         XPath.CONTAINS_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("substring-before"), XPath.SUBSTRING_BEFORE_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("substring-after"),  XPath.SUBSTRING_AFTER_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("substring"),        XPath.SUBSTRING_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("string-length"),    XPath.STRING_LENGTH_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("normalize-space"),  XPath.NORMALIZE_SPACE_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("translate"),        XPath.TRANSLATE_FUNCTION);

XPath.CORE_FUNCTIONS.registerFunction(new QName("boolean"),          XPath.BOOLEAN_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("not"),              XPath.NOT_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("true"),             XPath.TRUE_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("false"),            XPath.FALSE_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("lang"),             XPath.LANG_FUNCTION);

XPath.CORE_FUNCTIONS.registerFunction(new QName("number"),           XPath.NUMBER_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("sum"),              XPath.SUM_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("floor"),            XPath.FLOOR_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("ceiling"),          XPath.CEILING_FUNCTION);
XPath.CORE_FUNCTIONS.registerFunction(new QName("round"),            XPath.ROUND_FUNCTION);

XPathContext.prototype.functionResolvers.push(XPath.CORE_FUNCTIONS);