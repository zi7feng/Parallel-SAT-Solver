mod lib;

use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};
use lib::*;

const MAX_LIST_SIZE: usize = 200; // 3cnf 30 1000 sleep 2000
const MERGE_INTERVAL: Duration = Duration::from_millis(50000);
const TEST_ROUND: i32 = 30;

fn main() {
    let thread_number: Vec<i32> = vec![1, 2, 4, 8];
    let k = 70;
    for q in 31..=k {
        let mut j = 0;
        while j < thread_number.len() {
            let mut time_vec: Vec<f64> = Vec::new();
            let filename = format!("{}_{}.txt", q, thread_number[j].clone());
            let mut file = File::create(&filename).unwrap();
            let mut t = 0;
            while t < TEST_ROUND {
                let test_start = Instant::now();
                let path = &format!("benchmark/{}.cnf", q)[..];
                let formula = read_cnf_file(path);
                let mut assignment = initial_assignment(&formula);

                // Start the timer
                let mut start_time = Instant::now();

                // Preprocessing
                let simplified_formula = pure_literal_elimination(&formula, &mut assignment);
                let mut pre_formula: Vec<Vec<i32>> = Vec::new();

                let (mut result, mut simplified_formula, mut assignment) = unit_propagation(simplified_formula.clone(), &mut assignment);

                while pre_formula != simplified_formula.clone() {
                    pre_formula = simplified_formula.clone();
                    simplified_formula = pure_literal_elimination(&simplified_formula, &mut assignment);
                    let mut _temp_assignment = HashMap::new();
                    (result, simplified_formula, _temp_assignment) = unit_propagation(simplified_formula.clone(), &mut assignment);

                }

                if result != 0 {
                    let root = Arc::new(Node::new(
                        simplified_formula.clone(),
                        None,
                        0,
                        assignment.clone(),
                    ));

                    let mut threads = Vec::new();

                    let tasklist = Arc::new(Mutex::new(Vec::new()));
                    tasklist.lock().unwrap().push(root);
                    let flag = Arc::new(Mutex::new(false));

                    // Start the worker threads
                    for i in 0..thread_number[j] {
                        let tasklist = Arc::clone(&tasklist);
                        let flag = Arc::clone(&flag); // Clone the Arc
                        if i != 0 {
                            thread::sleep(Duration::from_millis(50));
                        }
                        if i == 0 {
                            let mut l_tasklist: Vec<Arc<Node>> = Vec::new();
                            let node = tasklist.lock().unwrap().pop().unwrap();
                            let result = build_search_tree(node.clone(), &mut l_tasklist);
                            tasklist.lock().unwrap().append(&mut l_tasklist);
                            if result {
                                // A solution was found, set the termination flag
                                *flag.lock().unwrap() = true;
                            }
                        }

                        threads.push(thread::spawn(move || {
                            let mut local_tasklist: Vec<Arc<Node>> = Vec::new();
                            let mut last_update_time = Instant::now();
                            let thread_id = i;

                            loop {
                                // Check the termination flag
                                if *flag.lock().unwrap() {
                                    break;
                                }
                                let node = match tasklist.lock().unwrap().pop() {
                                    Some(node) => {
                                        node
                                    }
                                    None => {
                                        if local_tasklist.len() == 0 {
                                            println!("no task");
                                            break;
                                        } else {
                                            println!("Thread {} add {}", thread_id, local_tasklist.len());

                                            tasklist.lock().unwrap().append(&mut local_tasklist);

                                            local_tasklist.clear();
                                        }
                                        continue;
                                    }
                                };

                                let result = build_search_tree(node.clone(), &mut local_tasklist);

                                // Check the termination flag
                                if *flag.lock().unwrap() {
                                    break;
                                }

                                if result {
                                    // A solution was found, set the termination flag
                                    *flag.lock().unwrap() = true;
                                    break;
                                }

                                let test_upbound = Instant::now();
                                if test_upbound - test_start > Duration::from_millis(50000) {
                                    start_time = Instant::now();
                                    println!("timeout");
                                    break;
                                }
                                if local_tasklist.len() >= MAX_LIST_SIZE || last_update_time.elapsed() >= MERGE_INTERVAL {
                                    tasklist.lock().unwrap().append(&mut local_tasklist);
                                    local_tasklist.clear();
                                    last_update_time = Instant::now();
                                }
                            }
                        }));
                    }

                    for thread in threads {
                        thread.join().unwrap();
                    }

                    if *flag.lock().unwrap() == false {
                        println!("UNSATISFIABLE");
                    }
                } else {
                    println!("UNSATISFIABLE");
                }


                // Stop the timer
                let end_time = Instant::now();

                let elapsed_time = end_time.duration_since(start_time).as_secs_f64() * 1000.0;

                if elapsed_time < Duration::from_millis(50000).as_secs_f64()*1000.0 {
                    time_vec.push(elapsed_time);
                    println!("{}", t.clone());
                }
                t += 1;
            }
            let data_str = time_vec.iter().map(|x| x.to_string()).collect::<Vec<_>>().join("\n");
            file.write_all(data_str.as_bytes()).unwrap();

            j += 1;
        }
    }
}