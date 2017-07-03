from java.lang import System
import sys
import random
import numpy as np
import tensorflow as tf

X = None
y = None
model = None
mean_loss = None
train_step = None
sess = None

def make(inputsize, hiddensize):
	global X, y, model
	tf.reset_default_graph()
	hiddensize = list(hiddensize)
	X = tf.placeholder(tf.float64, [None, inputsize])
	y = tf.placeholder(tf.float64, [None])
	out = X
	for i in range(len(hiddensize)):
		out = tf.layers.dense(out, hiddensize[i])
		out = tf.nn.relu(out)
	out = tf.layers.dense(out, 1)
	out = tf.reshape(out, [-1])
	model = out

def mean():
	global mean_loss
	global y, model
	mean_loss = tf.reduce_mean(tf.losses.mean_squared_error(y, model))

def opt():
	global mean_loss
	global train_step
	optimizer = tf.train.AdamOptimizer()
	extra_update_ops = tf.get_collection(tf.GraphKeys.UPDATE_OPS)
	with tf.control_dependencies(extra_update_ops):
		train_step = optimizer.minimize(mean_loss, tf.Variable(0.0, trainable = False))

def init():
	global sess
	sess = tf.Session()
	sess.run([tf.global_variables_initializer(), tf.local_variables_initializer()])

def train(X_train, y_train):
	global mean_loss
	global train_step
	global X, y, model
	global sess
	X_train = np.array(list(X_train)).reshape((50, -1))
	y_train = np.array(list(y_train))
	feed_dict = {X: X_train,
				 y: y_train}
	loss, _ = sess.run([mean_loss, train_step], feed_dict)
	return loss

def test(X_test):
	global X, y, model
	global sess
	feed_dict = {X: np.array([X_test]),
				 y: np.zeros(X[0].shape)}
	result = sess.run([model], feed_dict)
	System.out.println(result[0][0])
	return result[0][0]