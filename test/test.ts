import {expect} from 'chai';
import * as fs from 'fs';
import * as child_process from 'child_process';

// Change this function to run the particular MetaMath verifier you wish to test
function runTest(cwd, filename, done) {
  const cmd: string = __dirname + '/../../graphmm/vc/x64/Release/graphmm.exe ' + filename;

  child_process.exec(cmd, {cwd: cwd}, (err) => {
    done(err);
  });
}

const pathToTests = __dirname + '/../../metamath-test';

fs.readdir(pathToTests, (err: NodeJS.ErrnoException, files: string[]) => {
  if (err) {
    console.error('Expected to find directory "metamath-test" in the same parent directory as "checkmm-js"');
    console.error('git clone https://github.com/david-a-wheeler/metamath-test.git');
    process.exit(1);
  } else {
    describe('metamath-test', () => {

      files.forEach((filename: string) => {
        const pieces = filename.split('.');
        const ext = pieces[pieces.length - 1];
        pieces.pop();
        const fileTitle = pieces.join('.');
        const titlePieces = fileTitle.split('-');
        const last = titlePieces[titlePieces.length - 1];

        const expected: boolean = last.match('bad[1-9]*') ? false : true;

        if (ext === 'mm') {
          it(filename, (done) => {
            runTest(pathToTests, filename, (result) => {
              const succeeded = (result === null);
              expect(succeeded).to.equal(expected);
              done();
            });
          }).timeout(120000);
        }
      });

    });
    run();
  }
});

