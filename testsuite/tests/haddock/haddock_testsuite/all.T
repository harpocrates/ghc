test('haddockHtmlTest'  , [ignore_stdout, reqlib('xml')], makefile_test, ['htmlTest'  ])
test('haddockLatexTest' , [ignore_stdout, reqlib('xml')], makefile_test, ['latexTest' ])
test('haddockHoogleTest', [ignore_stdout, reqlib('xml')], makefile_test, ['hoogleTest'])
test('haddockHypsrcTest', [ignore_stdout, reqlib('xml')], makefile_test, ['hypsrcTest'])

