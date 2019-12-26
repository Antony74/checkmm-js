// Performs quadratic regression on regression test timings, comparing how long the js verifier takes
// compared to the cpp verifier I ported it from.  If the relationship is non-linear, we're in trouble!

import regression from 'regression';
import {performance} from 'perf_hooks';

import {getTests, runTest} from '../test/regression-tests';

class Task {
  filename: string;
  verifier: 'js' | 'cpp';
  expectedPass: boolean;
}

let tasks: Task[] = [];
const results = [];

getTests((err, files) => {
  if (err) {
    console.log(err.message);
    process.exit(1);
  } else {
    tasks = files.reduce(
      (acc, parsedFilename) => [
        ...acc,
        {filename: parsedFilename.filename, verifier: 'cpp', expectedPass: parsedFilename.expectedPass},
        {filename: parsedFilename.filename, verifier: 'js', expectedPass: parsedFilename.expectedPass}
      ],
      []
    );

    performTask();
  }
});

function performTask() {
  if (tasks.length) {
    const task: Task = tasks.shift();
    const start = performance.now();

    runTest(task.filename, task.verifier, (succeeded) => {

      const end = performance.now();
      const timeTaken = end - start;

      console.log(task.filename, task.verifier, timeTaken);

      if (succeeded !== task.expectedPass) {
        console.log('Unexpected test result');
        process.exit(1);
      }

      if (results.length && results[results.length - 1].length === 1) {
        results[results.length - 1].push(timeTaken);
      } else {
        results.push([timeTaken]);
      }

      performTask();
    });
  } else {
    tasksComplete();
  }
}

function tasksComplete() {
  console.log('tasks complete');
  console.log();

  const result = regression.polynomial(results, { order: 2, precision: 4 });

  console.log({string: result.string, equation: result.equation, r2: result.r2});
}

