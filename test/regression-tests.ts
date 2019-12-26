import {expect} from 'chai';
import * as fs from 'fs';
import * as child_process from 'child_process';

const pathToTests = __dirname + '/../../node_modules/metamath-test';

// Change this function to run the particular MetaMath verifier you wish to test
export function runTest(filename: string, done: (succeeded: boolean) => void) {

  let cmd: string = 'node ' + __dirname + '/../src/checkmm.js ' + filename;

  if (process.env.verifier.trim() === 'cpp') {
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
  if (filename !== 'anatomy-bad1.mm'
  &&  filename !== 'anatomy-bad2.mm'
  &&  filename !== 'anatomy-bad3.mm'
  &&  filename !== 'anatomy.mm'
  &&  filename !== 'big-unifier-bad1.mm'
  &&  filename !== 'big-unifier-bad2.mm'
  &&  filename !== 'big-unifier-bad3.mm'
  &&  filename !== 'big-unifier.mm'
  &&  filename !== 'demo0-bad1.mm'
  &&  filename !== 'demo0-includee.mm'
  &&  filename !== 'demo0-includer.mm'
  &&  filename !== 'demo0.mm'
  &&  filename !== 'emptyline.mm'
  &&  filename !== 'hol.mm') {
    return false;
  } else {
  return true;
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

