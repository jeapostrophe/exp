// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function XForms() {
};

XForms.BOOLEAN_FROM_STRING_FUNCTION = new XPathFunction(
  function(string) {
    string = XPath.STRING_FUNCTION.evaluate(string);

    switch (string.toLowerCase()) {
      case "true":  case "1": return true;
      case "false": case "0": return false;
      
      default:
        status("Bad call to boolean-from-string(\"" + string + "\")");
        throw new XFormsComputeException();
    }
  },
  
  XPathFunction.Context.NONE
);


XForms.IF_FUNCTION = new XPathFunction(
  function(condition, a, b) {
    condition = XPath.BOOLEAN_FUNCTION.evaluate(condition);
    
    return condition ? a : b;
  },
  
  XPathFunction.Context.NONE
);


XForms.AVG_FUNCTION = new XPathFunction(
  function(nodeSet) {
    return XPath.SUM_FUNCTION  .evaluate(nodeSet)
         / XPath.COUNT_FUNCTION.evaluate(nodeSet);
  },
  
  XPathFunction.Context.NONE
);


XForms.MIN_FUNCTION = new XPathFunction(
  function (nodeSet) {
    var setLen = nodeSet.length;
    if (setLen == 0) {
      return Number.NaN;
    }
    
    var minimum = XPathFunction.stringValueOf(nodeSet[0]);
    
    for (var i = setLen - 1; i >= 0; --i) {
      var value = XPath.NUMBER_FUNCTION.evaluate(XPathFunction.stringValueOf(nodeSet[i]));
      
      if (isNaN(value)) {
        return Number.NaN;
      }
      
      if (value < minimum) {
        minimum = value;
      }
    }
    
    return minimum;
  },
  
  XPathFunction.Context.NONE
);


XForms.MAX_FUNCTION = new XPathFunction(
  function (nodeSet) {
    var setLen = nodeSet.length;
    if (setLen == 0) {
      return Number.NaN;
    }
    
    var maximum = XPathFunction.stringValueOf(nodeSet[0]);
    
    for (var i = setLen - 1; i >= 0; --i) {
      var value = XPath.NUMBER_FUNCTION.evaluate(XPathFunction.stringValueOf(nodeSet[i]));
      
      if (isNaN(value)) {
        return Number.NaN;
      }
      
      if (value > maximum) {
        maximum = value;
      }
    }
    
    return maximum;
  },
  
  XPathFunction.Context.NONE
);


XForms.COUNT_NON_EMPTY_FUNCTION = new XPathFunction(
  function(nodeSet) {
    var count = 0;
    
    for (var i = nodeSet.length - 1; i >= 0; --i) {
      if (XPathFunction.stringValueOf(nodeSet[i]) != "") {
        ++count;
      }
    }
    
    return count;
  },
  
  XPathFunction.Context.NONE
);


XForms.INDEX_FUNCTION = new XPathFunction(
  function(repeatId) {
    repeatId = XPath.STRING_FUNCTION.evaluate(repeatId);

    return xform.getObjectById(repeatId, XFormRepeatControl).index + 1;
  },
  
  XPathFunction.Context.NONE
);


XForms.PROPERTY_FUNCTION = new XPathFunction(
  function(name) {
    name = XPath.STRING_FUNCTION.evaluate(name);
    
    switch (name) {
      case "version":           return "1.0";
      case "conformance-level": return "full";
    }
    
    throw new XFormsComputeException("Invalid property name: " + name);
  },
  
  XPathFunction.Context.NONE
);


XForms.NOW_FUNCTION = new XPathFunction(
  function() {
    // Pads out a number to the specified number of digits.
    //
    // Parameters:
    //     number: A number.
    //     digits: The minimum number of digits. If the number is not long enough,
    //             it is padded on the left with 0s.
    function padNumber(number, digits) {
      var string = number.toString();
      
      while (string.length < digits) {
        string = "0" + string;
      }
      
      return string;
    };
    
    var now = new Date();
    
    return padNumber(now.getUTCFullYear(),     4) + "-"
         + padNumber(now.getUTCMonth   () + 1, 2) + "-"
         + padNumber(now.getUTCDate    (),     2) + "T"
         + padNumber(now.getUTCHours   (),     2) + ":"
         + padNumber(now.getUTCMinutes (),     2) + ":"
         + padNumber(now.getUTCSeconds (),     2) + "Z";
  },
  
  XPathFunction.Context.NONE
);


XForms.DAYS_FROM_DATE_FUNCTION = new XPathFunction(
  function(date) {
    date = XPath.STRING_FUNCTION.evaluate(date);
    
    if (!date.match(/^(-?\d\d\d\d+)-(\d\d)-(\d\d)(?:T(\d\d):(\d\d):(\d\d(?:\.\d+)?))?(?:Z|([-+])(\d\d):(\d\d))?$/)) {
      return Number.NaN;
    }
    
    date = Date.UTC(RegExp.$1, RegExp.$2 - 1, RegExp.$3);
                     
    return date / 1000 / 60 / 60 / 24;
  },
  
  XPathFunction.Context.NONE
);


XForms.SECONDS_FROM_DATETIME_FUNCTION = new XPathFunction(
  function(date) {
    var zone = "";
    var date = XPath.STRING_FUNCTION.evaluate(date);
    
    if (!date.match(/^(-?\d\d\d\d+)-(\d\d)-(\d\d)T(\d\d):(\d\d):(\d\d(?:\.\d+)?)(?:Z|([-+])(\d\d):(\d\d))?$/)) {
      return Number.NaN;
    }
    
    date = date.split("T");
    zone = (date[1].split("Z").length > 1) ? date[1].split("Z")
         : (date[1].split("+").length > 1) ? date[1].split("+")
                                           : date[1].split("-");
    var date     = date[0].split("-");
    var time     = zone[0].split(":");
    var year     = +RegExp.$1;
    var month    = +RegExp.$2;
    var day      = +RegExp.$3;
    var hour     = +RegExp.$4; 
    var minute   = +RegExp.$5; 
    var second   = +RegExp.$6;
    var timeZone = [+RegExp.$7, +RegExp.$8, +RegExp.$9];
    
    if (timeZone[0] == "+") {
      hour   += timeZone[1];
      minute += timeZone[2];
      
      if (hour >= 24) {
        day  += 1;
        hour -= 24;
      }
      
      switch (month) {
        case 1: case 3: case 5: case 7: case 8: case 10: case 12:
          var daysInMonth = 31;
          break;
          
        case 2:
          var daysInMonth = (year % 4 != 0 || year % 100 == 0 || year % 400 != 0) ? 28 : 29;
          break;
        
        case 4: case 6: case 9: case 11:
          var daysInMonth = 30;
          break;
        
        default:
          assert(false, month + " is not a month");
      }
      
      if (day > daysInMonth) {
        month += 1;
        day   -= daysInMonth;
      }
      
      if (month > 12) {
        year  += 1;
        month -= 12;
      }
    }
    
    if (timeZone[0] == "-") {
      hour   -= (tz[1] == "30") ? (parseInt(tz[0]) + 1) : parseInt(tz[0]);
      minute += parseInt(tz[1]);
      
      if (hour < 0) {
        day  -= 1;
        hour += 24;
      }
      
      if (month == 3 && day < 1 && ((year % 4) == 0 && (year % 100) > 0)) {
        month -= 1;
        day   += 29;
      }
      
      if (month == 3 && day < 1) {
        month -= 1;
        day   += 28;
      }
      
      if ((month == 2 || month == 5 || month == 7 || month == 10) && day < 1) {
        month -= 1;
        day   += 30;
      }
      
      if (day < 1) {
        month -= 1;
        day   += 31;
      }
      
      if (month < 1) {
        year  -= 1;
        month += 12;
      }
    }
    
    date = Date.UTC(((date.length > 3) ? "-" : "") + year, month - 1, day, hour, minute, second);
    
    return date / 1000;
  },
  
  XPathFunction.Context.NONE
);


XForms.SECONDS_FUNCTION = new XPathFunction(
  function(durStr) {
    var d = XPath.STRING_FUNCTION.evaluate(durStr);

    if (d.match(/^-?P(?:(\d+)Y)?(?:(\d+)M)?(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+(?:\.\d+)?)S)?)?$/)) {
      var p = d.split("P");
      var t = p[1].split("T");
      var result = 0;
      var date = t[0];
      var time = (t[1]) ? t[1] : "";
      
      ((date.split("Y")).length > 1) ?  date = date.split("Y")[1] : date;
      ((date.split("M")).length > 1) ?  date = date.split("M")[1] : date;
      
      if ((date.split("D")).length > 1) {
        date = date.split("D");
        result += (parseInt(date[0]) * 60 * 60 * 24);
        date = date[1];
      }
      
      if ((time.split("H")).length > 1) {
        time = time.split("H");
        result += (parseInt(time[0]) * 60 * 60);
        time = time[1];
      }
      
      if ((time.split("M")).length > 1) {
        time = time.split("M");
        result += (parseInt(time[0]) * 60);
        time = time[1];
      }
      
      if ((time.split("S")).length > 1) {
        time = time.split("S");
        result += parseFloat(time[0]);
        time = time[1];
      }
      
      if (p[0] != "" && result != 0) {
        result = p[0] + result;
      }
      
      return result;
    }
    
    return "NaN";
  },
  
  XPathFunction.Context.NONE
);


XForms.MONTHS_FUNCTION = new XPathFunction(
  function(durStr) {
    var d = XPath.STRING_FUNCTION.evaluate(durStr);
    
    if (d.match(/^-?P(?:(\d+)Y)?(?:(\d+)M)?(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+(?:\.\d+)?)S)?)?$/)) {
      var p = d.split("P");
      var t = p[1].split("T");
      var result = 0;
      var date = t[0];
      
      if ((date.split("Y")).length > 1) {
        date = date.split("Y");
        result += (parseInt(date[0]) * 12);
        date = date[1];
      }
      
      if ((date.split("M")).length > 1) {
        date = date.split("M");
        result += parseInt(date[0]);
      }
      
      if (p[0] != "") {
        result = p[0] + result;
      }
      
      return result;
    }
    
    return "NaN";
  },
  
  XPathFunction.Context.NONE
);


XForms.INSTANCE_FUNCTION = new XPathFunction(
  function(idRef) {
    for (var i = xform.models.length - 1; i >= 0; --i) {
      var model = xform.models[i];
      
      for (var j = model.instances.length - 1; j >= 0; --j) {
        var instance = model.instances[j];
        
        if (instance.xmlElement.getAttribute("id") == idRef) {
          return new NodeSet([instance.document.documentElement]);
        }
      }
    }
    
    return new NodeSet();
  },
  
  XPathFunction.Context.NONE
);


XForms.FUNCTIONS = new XPathFunctionMap();

XForms.FUNCTIONS.registerFunction(new QName("boolean-from-string"),   XForms.BOOLEAN_FROM_STRING_FUNCTION);
XForms.FUNCTIONS.registerFunction(new QName("if"),                    XForms.IF_FUNCTION);
                                                                    
XForms.FUNCTIONS.registerFunction(new QName("avg"),                   XForms.AVG_FUNCTION);
XForms.FUNCTIONS.registerFunction(new QName("min"),                   XForms.MIN_FUNCTION);
XForms.FUNCTIONS.registerFunction(new QName("max"),                   XForms.MAX_FUNCTION);
XForms.FUNCTIONS.registerFunction(new QName("count-non-empty"),       XForms.COUNT_NON_EMPTY_FUNCTION);
XForms.FUNCTIONS.registerFunction(new QName("index"),                 XForms.INDEX_FUNCTION);
                                                                    
XForms.FUNCTIONS.registerFunction(new QName("property"),              XForms.PROPERTY_FUNCTION);
                                                                    
XForms.FUNCTIONS.registerFunction(new QName("now"),                   XForms.NOW_FUNCTION);
XForms.FUNCTIONS.registerFunction(new QName("days-from-date"),        XForms.DAYS_FROM_DATE_FUNCTION);
XForms.FUNCTIONS.registerFunction(new QName("seconds-from-dateTime"), XForms.SECONDS_FROM_DATETIME_FUNCTION);
XForms.FUNCTIONS.registerFunction(new QName("seconds"),               XForms.SECONDS_FUNCTION);
XForms.FUNCTIONS.registerFunction(new QName("months"),                XForms.MONTHS_FUNCTION);

XForms.FUNCTIONS.registerFunction(new QName("instance"),              XForms.INSTANCE_FUNCTION);

XPathContext.prototype.functionResolvers.push(XForms.FUNCTIONS);