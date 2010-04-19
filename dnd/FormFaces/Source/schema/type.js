// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function XmlSchemaType(name) {
  this.patterns = [];
  this.baseType = XmlSchemaType.prototype;
};

// Validates the value passed, returning an error message if the value is
// invalid or null if the value is valid.
//
// Checks that the value matches all of the patterns and enumeration facets
// defined for the type.
//
// Return value:
//     An error message if the value is invalid; otherwise, null.
XmlSchemaType.prototype.errorMessageFor = function(value) {
  value = this.canonicalValue(value);

  for (var i in this.patterns) {
    if (!value.match(this.patterns[i])) {
      return "%q is invalid.";
    }
  }

  if (this.enumeration != null) {
    var matched = false;

    for (var i in this.enumeration) {
      if (value == this.canonicalValue(this.enumeration[i])) {
        matched = true;
        break;
      }
    }

    if (!matched) {
      return "%q is not in the list of acceptable values.";
    }
  }

  return null;
};

// Validates the value passed.
//
// Return value:
//   True if the value is valid, false if not.
XmlSchemaType.prototype.isValid = function(value) {
  return this.errorMessageFor(value) == null;
};

// Given a valid value, returns the value in canonical form. Any values that are
// equal must have identical canonical values.
//
// The default implementation collapses/replaces white space based on the value
// of the whiteSpace facet.
//
// Return value:
//     The canonical form of the passed value.
XmlSchemaType.prototype.canonicalValue = function(value) {
  value = value.toString();

  switch (this.whiteSpace) {
    case "preserve":
      break;
      
    case "replace": 
      value = value.replace(/[\t\r\n]/g,   " ");
      break;
      
    case "collapse":
      value = value.replace(/[\t\r\n ]+/g, " ")
                   .replace(/^\s+|\s+$/g,  "");
                   
      break;
      
    default:
      assert(false, "bad whiteSpace value");
  }
  
  return value;
};

// Sets the value of one of the restriction facets.
//
// Return value:
//     The type object (this), allowing multiple facetXXX calls to be chained.
XmlSchemaType.prototype.facetLength         = function(length)         { this.length         = length;         return this; };
XmlSchemaType.prototype.facetMinLength      = function(minLength)      { this.minLength      = minLength;      return this; };
XmlSchemaType.prototype.facetMaxLength      = function(maxLength)      { this.maxLength      = maxLength;      return this; };
XmlSchemaType.prototype.facetWhiteSpace     = function(whiteSpace)     { this.whiteSpace     = whiteSpace;     return this; };
XmlSchemaType.prototype.facetMaxInclusive   = function(maxInclusive)   { this.maxInclusive   = maxInclusive;   return this; };
XmlSchemaType.prototype.facetMaxExclusive   = function(maxExclusive)   { this.maxExclusive   = maxExclusive;   return this; };
XmlSchemaType.prototype.facetMinInclusive   = function(minInclusive)   { this.minInclusive   = minInclusive;   return this; };
XmlSchemaType.prototype.facetMinExclusive   = function(minExclusive)   { this.minExclusive   = minExclusive;   return this; };
XmlSchemaType.prototype.facetTotalDigits    = function(totalDigits)    { this.totalDigits    = totalDigits;    return this; };
XmlSchemaType.prototype.facetFractionDigits = function(fractionDigits) { this.fractionDigits = fractionDigits; return this; };

// Adds a number of regular expressions to the pattern facet. A value is valid
// if it satisfies any one of the patterns.
//
// Parameters:
//      Any number of regular expression patterns.
//
// Return value:
//     The type object (this), allowing multiple facetXXX calls to be chained.
XmlSchemaType.prototype.facetPattern = function(/* pattern1, pattern2, ... */) {
  // For some reason, arguments.join doesn't work, so we'll make an array
  // containing the function arguments.
  var patterns = [];

  for (var i = 0; i < arguments.length; ++i) {
    patterns.push(arguments[i]);
  }

  this.patterns.push(new RegExp("^((" + patterns.join(")|(") + "))$"));
  
  return this;
};

// Sets a list of enumerated values allowed for the enumeration facet.
//
// Parameters:
//     Any number of allowed values.
//
// Return value:
//     The type object (this), allowing multiple facetXXX calls to be chained.
XmlSchemaType.prototype.facetEnumeration = function(/* enumeration1, enumeration2, ... */) {
  this.enumeration = [];

  for (var i = 0; i < arguments.length; ++i) {
    this.enumeration.push(arguments[i]);
  }

  return this;
};


// Returns a copy of the passed in type that can be further restricted.
XmlSchemaType.restrictionOf = function(baseType) {
  var type = {
    prototype: baseType
  };
  
  type.baseType = baseType;
  type.patterns = [];

  for (var i in baseType.patterns) {
    type.patterns.push(baseType.patterns[i]);
  }

  return type;
};

// Returns a new type that is the union of the passed in types.
XmlSchemaType.unionOf = function(/* type1, type2, ... */) {
  var type      = new XmlSchemaType();
  var baseTypes = arguments;

  // First call anyType.errorMessageFor. If that succeeds, call each of the base
  // type's errorMessageFor functions
  type.errorMessageFor = function(value) {
    for (var i = 0; i < baseTypes.length; ++i) {
      if (baseTypes[i].isValid(value)) {
        return null;
      }
    }

    return baseTypes[0].errorMessageFor(value);
  }

  return type;
};

// Creates a type that is a list of items of the specified type.
//
// Parameters:
//     itemType: The type of each item in the list.
XmlSchemaType.listOf = function(itemType) {
  var type = new XmlSchemaType()
    .facetWhiteSpace("collapse");

  type.errorMessageFor = function(value) {
    var items = this.baseType.canonicalValue.call(this, value).split(" ");

    // "".split(" ") returns [""], but we want [].
    if (items.length == 1 && items[0] == "") {
      items = [];
    }

    for (var i in items) {
      if (!itemType.isValid(items[i])) {
        return itemType.errorMessageFor(items[i]).replace(/%q/g, '"' + items[i] + '"');
      }
    }

    if (this.length != null) {
      if (items.length < this.length) {
        return "%q contains too few items.";
      }

      if (items.length > this.length) {
        return "%q contains too many items.";
      }
    }

    if (this.maxLength != null) {
      if (items.length > this.maxLength) {
        return "%q contains too many items.";
      }
    }

    if (this.minLength != null) {
      if (items.length < this.minLength) {
        return "%q contains too few items.";
      }
    }

    return null;
  };

  // Collapse the whitespace, then replace each list item with its canonical
  // value.
  type.canonicalValue = function(value) {
    var items = this.baseType.canonicalValue(value).split(" ");
    var value = "";

    for (var i in items) {
      if (i > 0) {
        value += " ";
      }

      value += itemType.canonicalValue(items[i]);
    }

    return value;
  };

  return type;
};


// Assigns a qualified name to a type; the type can later be retrieved by
// calling XmlSchemaType.get.
//
// Parameters:
//     name: A QualifiedName.
//
// Return value:
//     this, to allow other member function calls to be chained together.
XmlSchemaType.prototype.assignName = function(name) {
  if (typeof(XmlSchemaType.all) == "undefined") {
    XmlSchemaType.all = { };
  }
  
  XmlSchemaType.all[name.toString()] = this;
  
  return this;
};

// Gets the type with the specified name.
//
// Parameters:
//     name: A QualifiedName.
//
// Return value:
//     The named type, or null if there is none.
XmlSchemaType.get = function(name) {
  return XmlSchemaType.all[name.toString()];
};

// An object to provide quick access to the built-in XML Schema types.
var XmlSchemaTypes = { };