var source = require('vinyl-source-stream');
var buffer = require('vinyl-buffer');

var gulp = require('gulp');
var sourcemaps = require('gulp-sourcemaps');
var ts = require('gulp-typescript');
var babel = require('gulp-babel');
var rename = require('gulp-rename');
var uglify = require('gulp-uglify');
var gutil = require('gulp-util');

var watchify = require('watchify');
var browserify = require('browserify');
var babelify = require('babelify');

// Using my existing tsconfig.json file
var tsProject = ts.createProject(__dirname + '/tsconfig.json');

var babelBuildDir = '.babel-build';

gulp.task('ts-babel', function () {
  var compiledTs = tsProject.src()
        .pipe(ts(tsProject))
        .js;

  return compiledTs
    .pipe(babel())
    .pipe(rename(function(path) {
      path.extname = '.js';
    }))
    .pipe(gulp.dest(babelBuildDir));
});

// Dev
gulp.task('watch', ['ts-babel'], function() {
  gulp.watch('src/**/*.ts', ['ts-babel']);

  var b = watchify(browserify(wOpts));
  var runBundle = bundle.bind(null, b, false);
  b.on('update', runBundle);
  b.on('log', gutil.log);
  return runBundle();
});

var wOpts = {
  entries: [
    'node_modules/whatwg-fetch',
    'node_modules/webrtc-adapter',
    babelBuildDir + '/src/main.js'
  ],
  debug: true
};

function bundle(b, shallMinify) {
  function maybeMinify(x) {
    if (shallMinify) {
      return x.pipe(uglify().on('error', gutil.log));
    } else {
      return x;
    }
  }

  return maybeMinify(b.bundle()
                     .pipe(source('main.bundle.js'))
                     .pipe(buffer())  // Required by uglify.
                     .pipe(sourcemaps.init({loadMaps: true})))
    .pipe(sourcemaps.write('.'))  // Relative?
    .pipe(gulp.dest('static'));
}

// With minification.
gulp.task('bundle', ['ts-babel'], function() {
  return bundle(browserify(wOpts), true);
});
