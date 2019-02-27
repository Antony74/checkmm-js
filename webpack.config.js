'use strict';

module.exports = {
    devtool: 'inline-source-map',
    entry: './src/checkmmex.ts',
    module: {
        rules: [
            {
                test: /\.tsx?$/,
                loader: 'ts-loader'
            }
        ]
    },
    resolve: {
        extensions: [ '.ts', '.tsx', '.js' ]
    },
    node: {
      fs: 'empty'
    },
    output: {
      path: __dirname,
      filename: 'index.js',
      library: 'checkmm'
    }
};

