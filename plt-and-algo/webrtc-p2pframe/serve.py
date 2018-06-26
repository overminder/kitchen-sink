#!/usr/bin/env python3.5

import logging

import os
import sys
import random
import json
HERE = os.path.abspath(os.path.dirname(os.path.realpath(__file__)))

STATIC_PATH = os.path.join(HERE, 'static')

from tornado import gen
from tornado.websocket import WebSocketHandler
from tornado.web import Application, RequestHandler, StaticFileHandler
from tornado.ioloop import IOLoop

class Offer:
    resp_cb = None
    def __init__(self, key=None, offer_payload=None):
        self.key = key
        self.offer_payload = offer_payload
        self.candidates = []

    def __repr__(self):
        return '<Offer candidates=%d %r>' % (len(self.candidates), self.offer_payload)

    def wait_resp(self, callback=None):
        self.resp_cb = callback

class Offers:
    def __init__(self):
        self.offers = {}

    @classmethod
    def mkkey(cls):
        return str(random.randint(10000, 99999)) # Just to be simple.

    def add(self, offer):
        self.offers[offer.key] = offer
        return offer

    def find(self, key):
        return self.offers[key]

    def pop(self, key):
        return self.offers.pop(key)

offers = Offers()

class OfferListingHandler(RequestHandler):
    def get(self):
        self.write({
            'offers': [{'key': key, 'resp_cb': repr(resp_cb)}
                       for (key, resp_cb) in offers.offers.items()],
        })

class OfferHandler(WebSocketHandler):
    offer = None
    key = None

    def open(self):
        self.key = Offers.mkkey()

    def _ensure_offer(self):
        if self.offer is None:
            self.offer = Offer(key=self.key)
        return self.offer

    @gen.coroutine
    def on_message(self, s):
        msg = json.loads(s)
        print('msg', type(msg), repr(msg))
        if msg['type'] == 'allocKey':
            self.write_message({
                'type': 'allocKeyResp',
                'key': self.key,
            })
        elif msg['type'] == 'offer':
            offer = offers.add(self._ensure_offer())
            offer.offer_payload = msg
            self.write_message(json.dumps({
                'type': 'offer-created',
            }))
            resp = yield gen.Task(offer.wait_resp)
            self.write_message(json.dumps({
                'type': 'offer-accepted',
                'resp': resp,
            }))
        elif msg['type'] == 'take-offer':
            offer = offers.find(msg['key'])
            self.write_message(offer.offer_payload)
            for c in offer.candidates:
                self.write_message(c)
        elif msg['type'] == 'answer':
            key = msg.pop('forKey')
            offer = offers.pop(key)
            offer.resp_cb(msg)
        elif msg['type'] == 'candidate':
            self._ensure_offer().candidates.append(msg)

class NoCacheStaticFileHandler(StaticFileHandler):
     def set_extra_headers(self, path):
         self.set_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')

def mkapp():
    return Application([
        (r'/offer', OfferHandler),
        (r'/offers/list', OfferListingHandler),
        (r'/(.*)', NoCacheStaticFileHandler, {
            'path': STATIC_PATH,
        }),
    ], gzip=True)

def main():
    port = 17080
    mkapp().listen(port)
    print('Listening on :%d' % port)
    IOLoop.current().start()

if __name__ == '__main__':
    main()
