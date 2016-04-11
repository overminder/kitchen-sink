'use strict';

// module RN

var React = require('react-native');

exports.registerComponentF = function(name, component) {
  return function() {
    React.AppRegistry.registerComponent(name, function() {
      return component;
    });
  };
};

exports.createStyleSheetF = function(name, value) {
  return function() {
    var key = 'anonymous';
    var sheetObj = {};
    sheetObj[key] = value;
    var sheet = React.StyleSheet.create(sheetObj);
    return sheet[key];
  };
};

exports.viewClass = React.View;
exports.textClass = React.Text;
exports.touchableOpacityClass = React.TouchableOpacity;
