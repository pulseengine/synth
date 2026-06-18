.syntax unified
.thumb
.global k_spin_lock, k_spin_unlock, z_ready_thread, z_reschedule
.global z_thread_return_value_set_with_data, z_unpend_first_thread
.thumb_func
k_spin_lock:
k_spin_unlock:
z_ready_thread:
z_reschedule:
z_thread_return_value_set_with_data:
z_unpend_first_thread:
  bx lr
