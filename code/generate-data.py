#!/usr/local/bin/python

from __future__ import print_function
from easyprocess import EasyProcess

import os
import csv
from os.path import splitext, join
import subprocess
import sys
import time

from math import sqrt

def stddev(lst):
    mean = float(sum(lst)) / len(lst)
    return sqrt(float(reduce(lambda x, y: x + y, map(lambda x: (x - mean) ** 2, lst))) / len(lst))

def average(lst):
    return sum(lst)/len(lst)


TEST_EXT = '.ds'
REF_EXT = '.out'
BASELINE_EXT = '.out'
BASE_FLAGS = ["-print-data"]
TIMEOUT_TIME = 1805
STILL_WORK_TIMEOUT_TIME = 120
GENERATE_EXAMPLES_TIMEOUT_TIME = 600000

REPETITION_COUNT = 10

def ensure_dir(f):
    d = os.path.dirname(f)
    if not os.path.exists(d):
        os.makedirs(d)

def transpose(matrix):
    return zip(*matrix)

def check_equal(path,base,data):
    with open(join(path,base + REF_EXT), "r") as exfile:
        return exfile.read() == data

def find_tests(root):
    tests = []
    for path, dirs, files in os.walk(root):
        files = [(f[0], f[1]) for f in [splitext(f) for f in files]]
        tests.extend([(path, f[0]) for f in files if f[1] == TEST_EXT])
    return tests

def gather_datum(prog, path, base, additional_flags, timeout):
    start = time.time()
    flags = additional_flags
    #flags = map(lambda t: t(path,base),additional_flags)
    process_output = EasyProcess([prog] + BASE_FLAGS + flags + [join(path, base + TEST_EXT)]).call(timeout=timeout)
    end = time.time()
    return ((end - start), process_output.stdout,process_output.stderr)


def gather_data(rootlength, prog, path, base):
    current_data = {"Test":join(path, base).replace("_","-")[rootlength:]}

    def gather_col(flags, run_combiner, col_names, timeout_time, repetition_count, compare):
        print(col_names)
        run_data = []
        timeout = False
        error = False
        incorrect = False
        for iteration in range(repetition_count):
            (time,datum,err) = gather_datum(prog, path, base,flags,timeout_time)
            if err != "":
                print(err)
                error = True
                break
            if time >= TIMEOUT_TIME - 5:
                timeout = True
                break
            this_run_data = [time] + map(lambda d: d.strip(),datum.split(";"))
            if not check_equal(path,base,this_run_data[1]) and compare:
                incorrect = True
            run_data.append(this_run_data)
        if error:
            print("error")
            for col_name in col_names:
                current_data[col_name]="error"
        elif timeout:
            print("timeout")
            for col_name in col_names:
                current_data[col_name]="timeout"
        elif incorrect:
            print("incorrect")
            for col_name in col_names:
                current_data[col_name]="incorrect"
        else:
            run_data_transpose = transpose(run_data)
            print(run_data_transpose)
            combined_data = run_combiner(run_data_transpose)
            for (col_name,data) in zip(col_names,combined_data):
                current_data[col_name] = data

    def ctime_combiner(run_data_transpose):
        computation_time_col = [float(x) for x in run_data_transpose[0]]
        synthesis_calls_col = [int(x) for x in run_data_transpose[2]]
        verification_calls_col = [int(x) for x in run_data_transpose[3]]
        max_synth_time_calls = [float(x) for x in run_data_transpose[4]]
        max_verif_time_calls = [float(x) for x in run_data_transpose[5]]
        total_synth_time = [float(x) for x in run_data_transpose[6]]
        total_verif_time = [float(x) for x in run_data_transpose[7]]
        invariant_size_col = [int(x) for x in run_data_transpose[8]]
        average_computation = average(computation_time_col)
        synth_calls = synthesis_calls_col[0]
        verif_calls = verification_calls_col[0]
        average_max_synth = average(max_synth_time_calls)
        average_max_verif = average(max_verif_time_calls)
        average_total_synth_time = average(total_synth_time)
        average_total_verif_time = average(total_verif_time)
        invariant_size = invariant_size_col[0]
        return [average_computation,synth_calls,verif_calls,average_max_synth,average_max_verif,average_total_synth_time,average_total_verif_time,invariant_size]

    def exs_reqd_combiner(run_data_transpose):
        example_number_col = [float(x) for x in run_data_transpose[0]]
        return "{:.1f}".format(sum(example_number_col)/len(example_number_col))

    def max_exs_reqd_combiner(run_data_transpose):
        example_number_col = [float(x) for x in run_data_transpose[0]]
        return int(sum(example_number_col)/len(example_number_col))

    def specsize_combiner(run_data_transpose):
        print(run_data_transpose[1])
        example_number_col = [float(x) for x in run_data_transpose[1]]
        return int(sum(example_number_col)/len(example_number_col))


    #gather_col([],ctime_combiner,"SS",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col([],ctime_combiner,"Full",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col([lambda p, b: "-a",lambda p, b: join(p, b + ".accum"), lambda p, b: "-prelude-context"],ctime_combiner,"FullP",TIMEOUT_TIME,REPETITION_COUNT)
        return [average_computation,synth_calls,verif_calls,average_max_synth,average_max_verif,average_total_synth_time,average_total_verif_time]
    gather_col([],ctime_combiner,["MythTime","MythSynthCalls","MythVerifCalls","MythMaxSynthTime","MythMaxVerifTime","MythTotalSynthTime","MythTotalVerifTime","InvariantSize"],TIMEOUT_TIME,REPETITION_COUNT,True)
    gather_col(["-use-fold"],ctime_combiner,["FoldTime","FoldSynthCalls","FoldVerifCalls","FoldMaxSynthTime","FoldMaxVerifTime","FoldTotalSynthTime","FoldTotalVerifTime"],TIMEOUT_TIME,REPETITION_COUNT,False)
    gather_col(["-smallestthirty"],ctime_combiner,["ThirtyTime","ThirtySynthCalls","ThirtyVerifCalls","ThirtyMaxSynthTime","ThirtyMaxVerifTime","ThirtyTotalSynthTime","ThirtyTotalVerifTime"],TIMEOUT_TIME,REPETITION_COUNT,False)
    gather_col(["-srp"],ctime_combiner,["SRPTime","SRPSynthCalls","SRPVerifCalls","SRPMaxSynthTime","SRPMaxVerifTime","SRPTotalSynthTime","SRPTotalVerifTime"],TIMEOUT_TIME,REPETITION_COUNT,False)
    gather_col(["-clp"],ctime_combiner,["CLPTime","CLPSynthCalls","CLPVerifCalls","CLPMaxSynthTime","CLPMaxVerifTime","CLPTotalSynthTime","CLPTotalVerifTime"],TIMEOUT_TIME,REPETITION_COUNT,False)
    gather_col(["-conj-str"],ctime_combiner,["ConjStrTime","ConjStrSynthCalls","ConjStrVerifCalls","ConjStrMaxSynthTime","ConjStrMaxVerifTime","ConjStrTotalSynthTime","ConjStrTotalVerifTime"],TIMEOUT_TIME,REPETITION_COUNT,False)
    gather_col(["-linear-arbitrary"],ctime_combiner,["LAStrTime","LAStrSynthCalls","LAStrVerifCalls","LAStrMaxSynthTime","LAStrMaxVerifTime","LAStrTotalSynthTime","LAStrTotalVerifTime"],TIMEOUT_TIME,REPETITION_COUNT,False)
    #gather_col([lambda p, b: "-use-myth", lambda p, b: "-prelude-context"],ctime_combiner,"MythP",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col([lambda p, b: "-a",lambda p, b: join(p, b + ".accum"), lambda p, b: "-gat"],ctime_combiner,"GAT",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col([lambda p, b: "-a",lambda p, b: join(p, b + ".accum"), lambda p, b: "-no-dedup"],ctime_combiner,"NDD",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col([lambda p, b: "-a",lambda p, b: join(p, b + ".accum")],ctime_combiner,"PAT",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(["-noCS"],ctime_combiner,"SSNC",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(["-bijSynth"],ctime_combiner,"BS",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(["-bijSynth","-noCS"],ctime_combiner,"BSNC",TIMEOUT_TIME,REPETITION_COUNT)
    ##gather_col(["-noKeepGoing"],ctime_combiner,"NoTP",TIMEOUT_TIME,1)
    ##gather_col(["-twentyfivetc"],ctime_combiner,"TC25",TIMEOUT_TIME,1)
    ##gather_col(["-negtwentyfivetc"],ctime_combiner,"TCN25",TIMEOUT_TIME,1)
    #gather_col(["-noTerminationCondition"],ctime_combiner,"FC",TIMEOUT_TIME,1)
    #gather_col(["-dumbCost"],ctime_combiner,"NM",TIMEOUT_TIME,1)
    #gather_col(["-dumbCostCorrectPair"],ctime_combiner,"NMCC",TIMEOUT_TIME,1)
    #gather_col(["-constantCost"],ctime_combiner,"ConstCost",TIMEOUT_TIME,1)
    #gather_col(["-constantCostCorrectPair"],ctime_combiner,"ConstCostCC",TIMEOUT_TIME,1)
    #gather_col(["-noSkip"],ctime_combiner,"NoSkip",TIMEOUT_TIME,1)
    #gather_col(["-noRequire"],ctime_combiner,"NoRequire",TIMEOUT_TIME,1)
    #gather_col(["-regexSize"],specsize_combiner,"RegexSize",TIMEOUT_TIME,1)
    #gather_col(["-lensSize"],specsize_combiner,"LensSize",TIMEOUT_TIME,1)
    ##gather_col(['-forceexpand','-time'],ctime_combiner,"ForceExpandTime",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-naive_strategy','-time'],ctime_combiner,"NaiveStrategy",TIMEOUT_TIME,REPETITION_COUNT)
    ##gather_col(['-naive_pqueue','-time'],ctime_combiner,"NaivePQueue",TIMEOUT_TIME,REPETITION_COUNT)
    ##gather_col(['-no_short_circuit','-time'],ctime_combiner,"NoShortCircuit",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-no_lens_context','-time'],ctime_combiner,"NoLensContext",TIMEOUT_TIME,REPETITION_COUNT)
    ##gather_col(['-no_short_circuit','-no_inferred_expansions','-no_lens_context','-time'],ctime_combiner,"NoInferenceNoLCNoSC",TIMEOUT_TIME,REPETITION_COUNT)
    ##gather_col(['-no_short_circuit','-no_lens_context','-time'],ctime_combiner,"NoLCNoSC",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-naive_expansion_search','-no_lens_context','-time'],ctime_combiner,"NaiveExpansionNoLC",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-use_only_forced_expansions','-no_lens_context','-time'],ctime_combiner,"OnlyForcedExpansionsNoLC",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-naive_expansion_search','-time'],ctime_combiner,"NaiveExpansion",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-use_only_forced_expansions','-time'],ctime_combiner,"OnlyForcedExpansions",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-forceexpand','-naive_expansion_search','-time'],ctime_combiner,"NoUDTypes",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-generatedexamples'],exs_reqd_combiner,"ExamplesRequired",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-max_to_specify'],max_exs_reqd_combiner,"MaxExampleCount",TIMEOUT_TIME,1)
    #gather_col(['-spec_size'],max_exs_reqd_combiner,"SpecSize",TIMEOUT_TIME,1)
    #gather_col(['-lens_size'],max_exs_reqd_combiner,"LensSize",TIMEOUT_TIME,1)
    #gather_col(['-examples_count'],max_exs_reqd_combiner,"ExamplesCount",TIMEOUT_TIME,1)
    #gather_col(['-lens_size','-no_simplify_generated_lens'],max_exs_reqd_combiner,"LensSizeNoMinimize",TIMEOUT_TIME,1)
    #gather_col(['-lens_and_spec_size'],max_exs_reqd_combiner,"LensAndSpecSize",TIMEOUT_TIME,1)
    #gather_col(['-possible_lenses_ex', '0', '5'],max_exs_reqd_combiner,"ZeroExamplesPossibilities",TIMEOUT_TIME,1)
    #gather_col(['-possible_lenses_ex', '2', '5'],max_exs_reqd_combiner,"TwoExamplesPossibilities",TIMEOUT_TIME,10)
    #gather_col(['-possible_lenses_ex', '5', '5'],max_exs_reqd_combiner,"FiveExamplesPossibilities",TIMEOUT_TIME,10)
    #gather_col(['-compositional_lenses_used'],max_exs_reqd_combiner,"CompositionalLensesUsed",TIMEOUT_TIME,1)
    #gather_col(['-lens_size','-no_lens_context'],max_exs_reqd_combiner,"LensSizeNoLensContext",TIMEOUT_TIME,1)
    #gather_col(['-expansions_inferred'],max_exs_reqd_combiner,"ExpansionsInferred",TIMEOUT_TIME,1)
    #gather_col(['-expansions_inferred','-no_lens_context'],max_exs_reqd_combiner,"ExpansionsInferredNoLensContext",TIMEOUT_TIME,1)
    #gather_col(['-expansions_forced'],max_exs_reqd_combiner,"ExpansionsForced",TIMEOUT_TIME,1)
    #gather_col(['-expansions_forced','-no_lens_context'],max_exs_reqd_combiner,"ExpansionsForcedNoLensContext",TIMEOUT_TIME,1)
    #gather_col(['-specs_visited'],max_exs_reqd_combiner,"SpecsVisited",TIMEOUT_TIME,1)
    #gather_col(['-specs_visited','-naive_expansion_search'],max_exs_reqd_combiner,"SpecsVisitedNaiveExpansion",TIMEOUT_TIME,1)
    #gather_col(['-specs_visited','-use_only_forced_expansions'],max_exs_reqd_combiner,"SpecsVisitedOnlyForcedExpansions",TIMEOUT_TIME,1)
    #gather_col(['-specs_visited','-no_lens_context'],max_exs_reqd_combiner,"SpecsVisitedNoLensContext",TIMEOUT_TIME,1)
    #gather_col(['-expansions_performed'],max_exs_reqd_combiner,"ExpansionsPerformed",TIMEOUT_TIME,1)
    #gather_col(['-expansions_performed','-no_lens_context'],max_exs_reqd_combiner,"ExpansionsPerformedNoLensContext",TIMEOUT_TIME,1)
    ##gather_col(['-naive_pqueue','-no_lens_context','-time'],ctime_combiner,"NoLensContextNPQ",TIMEOUT_TIME,REPETITION_COUNT)
    ##gather_col(['-naive_pqueue','-no_short_circuit','-no_inferred_expansions','-no_lens_context','-time'],ctime_combiner,"NoInferenceNoLCNoSCNPQ",TIMEOUT_TIME,REPETITION_COUNT)
    ##gather_col(['-naive_pqueue','-no_short_circuit','-no_lens_context','-time'],ctime_combiner,"NoLCNoSCNPQ",TIMEOUT_TIME,REPETITION_COUNT)
    ##gather_col(['-naive_pqueue','-no_inferred_expansions','-no_lens_context','-time'],ctime_combiner,"NoInferenceNoLCNPQ",TIMEOUT_TIME,REPETITION_COUNT)

    return current_data

def extract_test(x):
    return x["Test"]

def specsize_compare(x,y):
    return int(x["SpecSize"])-int(y["SpecSize"])

def test_compare(x,y):
    return int(x["Test"])-int(y["Test"])

def sort_data(data):
    data.sort(key=extract_test)#sorted(data,cmp=test_compare)

def print_data(data):
    print(data)
    ensure_dir("generated_data/")
    with open("generated_data/generated_data.csv", "wb") as csvfile:
        datawriter = csv.DictWriter(csvfile,fieldnames=data[0].keys())
        datawriter.writeheader()
        datawriter.writerows(data)

def print_usage(args):
    print("Usage: {0} <prog> <test|testdir>".format(args[0]))

def transform_data(path, base, run_data):
    current_data = {"Test":join(path, base + TEST_EXT).replace("_","-")[6:]}
    run_data_transpose = transpose(run_data)
    for index in range(len(run_data_transpose)/2):
        col_name = run_data_transpose[index][0]
        col_data = run_data_transpose[index+1]
        if "" in col_data:
            current_data[col_name]=-1
        else:
            col = [float(x) for x in col_data]
            current_data[col_name] = str(sum(col)/len(col))
    return current_data

def load_data():
    try:
        with open("generated_data/generated_data.csv", "r") as csvfile:
            datareader = csv.DictReader(csvfile)
            return [row for row in datareader]
    except:
        return []

def main(args):
    if len(args) == 3:
        prog = args[1]
        path = args[2]
        rootlength = len(path)
        data = load_data()
        print(data)
        if not os.path.exists(prog):
            print_usage(args)
        elif os.path.exists(path) and os.path.isdir(path):
            for path, base in find_tests(path):
                test_name = join(path, base).replace("_","-")[rootlength:]
                print(test_name)
                if (not (any(row["Test"] == test_name for row in data))):
                    current_data = gather_data(rootlength,prog, path, base)
                    data.append(current_data)
                    print_data(data)
                else:
                    print("data already retrieved")
            sort_data(data)
            print_data(data)
        else:
            path, filename = os.path.split(path)
            base, ext = splitext(filename)
            if ext != TEST_EXT:
                print_usage(args)
            else:
                data = gather_data(prog, path, base)
                sort_data(data)
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
