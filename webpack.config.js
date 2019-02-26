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
    externals: {
      'lodash.clonedeep': 'lodash.clonedeep',
      'node-fetch': 'node-fetch'
      },
    output: {
      path: __dirname,
      filename: 'index.js'
    }
};

