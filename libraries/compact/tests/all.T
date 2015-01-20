def compact_setup(name, opts):
    extra_run_opts('+RTS -xs1 -RTS')(name, opts)
    omit_ways('ghci')(name, opts)

setTestOpts(compact_setup)
test('compact_simple', normal, compile_and_run, [''])
test('compact_loop', normal, compile_and_run, [''])
test('compact_append', normal, compile_and_run, [''])
test('compact_autoexpand', normal, compile_and_run, [''])
test('compact_simple_array', normal, compile_and_run, [''])