/*
 * BLS handler wrappers. Each function parses Python arguments, marshals
 * them into Lean runtime objects, invokes the corresponding `@[export]`-d
 * `eth_bls_*` symbol, and unwraps the IO result back to Python.
 */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_bls_aggregate_pubkeys(
  lean_object* pubkeys,
  lean_object* world
);

extern lean_object*
eth_bls_fast_aggregate_verify(
  lean_object* pubkeys,
  lean_object* msg,
  lean_object* sig,
  lean_object* world
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_eth_aggregate_pubkeys(
  PyObject* self,
  PyObject* args
) {
  PyObject* pubkeys_obj;
  if (!PyArg_ParseTuple(args, "O", &pubkeys_obj)) return NULL;
  Py_ssize_t n;
  uint8_t* pks = pack_bytes_sequence(pubkeys_obj, BYTES_PER_PUBKEY, &n, "pubkey");
  if (!pks) return NULL;

  uint8_t out[BYTES_PER_PUBKEY];
  lean_object* res = eth_bls_aggregate_pubkeys(
    mk_bytearray_array(pks, n, BYTES_PER_PUBKEY),
    lean_io_mk_world());
  PyMem_Free(pks);
  if (run_io_into_bytearray(res, out, BYTES_PER_PUBKEY)) {
    PyErr_SetString(PyExc_RuntimeError, "eth_aggregate_pubkeys failed");
    return NULL;
  }
  return PyBytes_FromStringAndSize((const char*) out, BYTES_PER_PUBKEY);
}

PyObject*
py_eth_fast_aggregate_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pubkeys_obj, *msg_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOO", &pubkeys_obj, &msg_obj, &sig_obj)) return NULL;
  if (!PyBytes_Check(msg_obj)) {
    PyErr_SetString(PyExc_TypeError, "message must be bytes");
    return NULL;
  }
  if (!PyBytes_Check(sig_obj)) {
    PyErr_SetString(PyExc_TypeError, "signature must be bytes");
    return NULL;
  }
  Py_ssize_t n;
  uint8_t* pks = pack_bytes_sequence(pubkeys_obj, BYTES_PER_PUBKEY, &n, "pubkey");
  if (!pks && PyErr_Occurred()) return NULL;
  /* `pack_bytes_sequence` returns NULL with no error on an empty sequence. */
  if (!pks) {
    pks = (uint8_t*) PyMem_Malloc(1);
    if (!pks) return PyErr_NoMemory();
    n = 0;
  }

  Py_ssize_t msg_len = PyBytes_GET_SIZE(msg_obj);
  Py_ssize_t sig_len = PyBytes_GET_SIZE(sig_obj);
  const uint8_t* msg = (const uint8_t*) PyBytes_AS_STRING(msg_obj);
  const uint8_t* sig = (const uint8_t*) PyBytes_AS_STRING(sig_obj);

  uint8_t ok = 0;
  lean_object* res = eth_bls_fast_aggregate_verify(
    mk_bytearray_array(pks, n, BYTES_PER_PUBKEY),
    mk_bytearray(msg, msg_len),
    mk_bytearray(sig, sig_len),
    lean_io_mk_world());
  PyMem_Free(pks);
  if (run_io_into_bool(res, &ok)) {
    PyErr_SetString(PyExc_RuntimeError, "eth_fast_aggregate_verify failed");
    return NULL;
  }
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}
