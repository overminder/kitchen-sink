var path = require('path');

function here(relpath) {
  return path.join(__dirname, relpath);
}

// See https://webpack.github.io/docs/tutorials/getting-started/
// , https://www.typescriptlang.org/docs/handbook/integrating-with-build-tools.html
// and https://webpack.github.io/docs/multiple-entry-points.html

module.exports = {
    entry: {
        web: here('src/web/main.tsx'),
        backend: here('src/backend/main.tsx'),
    },
    output: {
        path: here('dist'),
        filename: '[name].bundle.js',
    },
    resolve: {
        // Add '.ts' and '.tsx' as a resolvable extension.
        extensions: ['', '.webpack.js', '.web.js', '.ts', '.tsx', '.js'],
    },
    module: {
        loaders: [
            // all files with a '.ts' or '.tsx' extension will be handled by 'ts-loader'
            { test: /\.tsx?$/, loader: 'ts-loader' },
        ],
    },
}
