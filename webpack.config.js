
module.exports = {
  entry: './src/checkmmex.ts',
  output: {
    filename: 'index.js',
    path: __dirname
  },
  node: {
    fs: "empty"
  },
  module: {
    rules: [
      {
        test: /\.tsx?$/,
        use: 'ts-loader',
        exclude: /node_modules/
      }
    ]
  },
  resolve: {
    extensions: ['.tsx', '.ts', '.js']
  },
  devtool: 'source-map'
};

