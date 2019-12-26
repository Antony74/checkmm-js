import {expect} from 'chai';
import * as fs from 'fs';
import * as child_process from 'child_process';
import * as path from 'path';

const pathToTests = __dirname + '/../../node_modules/metamath-test';
const defaultVerifier = typeof(process.env.verifier) === 'string' ? process.env.verifier.trim() : 'js';

// Change this function to run the particular MetaMath verifier you wish to test
export function runTest(filename: string, verifier: string, done: (succeeded: boolean) => void) {

  let cmd: string = 'node ' + __dirname + '/../src/checkmm.js ' + filename;

  if (verifier === 'cpp') {
    cmd = __dirname + '/../../../graphmm/vc/x64/Release/graphmm.exe ' + filename;
  }

  child_process.exec(cmd, {cwd: pathToTests}, (err) => {
    done(err === null);
  });
}

class ParsedFilename {
  filename: string;
  isMM: boolean;
  expectedPass: boolean;
}

function parseFilename(filename: string): ParsedFilename {
  const pieces = filename.split('.');
  const ext = pieces.pop();
  const fileTitle = pieces.join('.');
  const titlePieces = fileTitle.split('-');
  const last = titlePieces.pop();

  const expectedPass: boolean = last.match('bad[1-9]*') ? false : true;

  // This test is a special case.  It is meant to fail but doesn't
  // follow the pattern of other fails.
  // https://github.com/david-a-wheeler/metamath-test/issues/3
  const normalPassCriteria: boolean = (filename !== 'set-dist.mm');

  return {
    filename: filename,
    isMM: (ext === 'mm'),
    expectedPass: (normalPassCriteria && expectedPass)
  };

}

function isFastTest(filename) {
  // Restrict which tests are run until I can improve performance
  if (filename !== 'set.mm'
  &&  filename !== 'set.2010-08-29.mm') {
    return true;
  } else {
    return false;
  }
}

export function getTests(callback: (err: NodeJS.ErrnoException, files: ParsedFilename[]) => void) {

  fs.readdir(pathToTests, (err: NodeJS.ErrnoException, files: string[]) => {
    if (err) {
      callback(err, []);
    } else {
      callback(
        null,
        files
          .filter(isFastTest)
          .map((filename: string) => parseFilename(filename))
          .filter((parsedFilename) => parsedFilename.isMM)
      );
    }
  });

}

// Are we being run in mocha?
if (path.basename(process.argv[1]) === 'mocha') {

  getTests((err: NodeJS.ErrnoException, files: ParsedFilename[]) => {

    if (err) {
      console.log(err.message);
      process.exit(1);
    } else {
      describe('metamath-test', () => {

        files.forEach((parsedFilename) => {

          const filename = parsedFilename.filename;

          it(filename, (done) => {

            runTest(
              filename,
              defaultVerifier,
              (succeeded) => {
                expect(succeeded).to.equal(parsedFilename.expectedPass);
                done();
              }
            );

          }).timeout(600000);

        });
      });

      run();

    }
  });
}

