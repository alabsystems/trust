# SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
#
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

# see https://sourceware.org/gdb/current/onlinedocs/gdb.html/Writing-a-Pretty_002dPrinter.html

import gdb

class EnumClassPrettyPrinter(gdb.ValuePrinter):
    def __init__(self, val):
        self.__val = val

    def to_string(self):
        return str(self.__val.cast(gdb.lookup_type('uint32_t')))


def register_tpde_printers():
    pp = gdb.printing.RegexpCollectionPrettyPrinter('tpde')
    pp.add_printer('blockIndex', '^tpde::Analyzer<.*>::BlockIndex', EnumClassPrettyPrinter)
    pp.add_printer('valLocalIndex', '^tpde::CompilerBase<.*>::ValLocalIdx', EnumClassPrettyPrinter)
    pp.add_printer('testValueRef', '^tpde::test::TestIRAdaptor::IRValueRef', EnumClassPrettyPrinter)
    pp.add_printer('testBlockRef', '^tpde::test::TestIRAdaptor::IRBlockRef', EnumClassPrettyPrinter)
    pp.add_printer('testFuncRef', '^tpde::test::TestIRAdaptor::IRFuncRef', EnumClassPrettyPrinter)
    gdb.printing.register_pretty_printer(gdb.current_objfile(), pp)