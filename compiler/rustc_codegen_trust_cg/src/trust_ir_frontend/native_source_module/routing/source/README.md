# Closure-free native source regression inputs

The four inputs now live in the executable run-make regression
[`tests/run-make/trust-cg-native-source-routes`](../../../../../../../tests/run-make/trust-cg-native-source-routes/README.md).
That fixture requires strict whole-object certificates and actual native
execution at O0/O3, including the full Darwin C-u8 W0 contract. Its execution
must use a matching rebuilt SDK/backend; pure routing tests remain separate.
