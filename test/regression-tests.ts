import {expect} from 'chai';
import * as fs from 'fs';
import * as child_process from 'child_process';

// Change this function to run the particular MetaMath verifier you wish to test
function runTest(cwd: string, filename: string, done: (succeeded: boolean) => void) {

  let cmd: string = 'node ' + __dirname + '/../src/checkmm.js ' + filename;

  if (process.env.verifier.trim() === 'cpp') {
    cmd = __dirname + '/../../../graphmm/vc/x64/Release/graphmm.exe ' + filename;
  }

  child_process.exec(cmd, {cwd: cwd}, (err) => {
    done(err === null);
  });
}

class ParsedFilename {
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
    isMM: (ext === 'mm'),
    expectedPass: (normalPassCriteria && expectedPass)
  };

}

const pathToTests = __dirname + '/../../node_modules/metamath-test';

fs.readdir(pathToTests, (err: NodeJS.ErrnoException, files: string[]) => {
  if (err) {
    console.log(err.message);
    process.exit(1);
  } else {
    describe('metamath-test', () => {

      files.forEach((filename: string) => {

        const parsed: ParsedFilename = parseFilename(filename);

        if (parsed.isMM) {

          it(filename, (done) => {

            runTest(pathToTests, filename, (succeeded) => {
              expect(succeeded).to.equal(parsed.expectedPass);
              done();
            });

          }).timeout(120000);

        }
      });
    });

    run();
  }
});

