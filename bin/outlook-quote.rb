#!/usr/bin/env ruby
# Fix outlook quoting. Inspired by perl original by Kevin D. Clark.
# This program is meant to be used as a text filter. It reads a plaintext
# outlook-formatted email and fixes the quoting to the "internet style",
# so that::
#
#   -----Original Message-----
#   [from-header]: Blah blah
#   [timestamp-header]: day month etc
#   [...]
#
#   message text
#
# or::
#
#   ___________________________
#   [from-header]: Blah blah
#   [timestamp-header]: day month etc
#   [...]
#
#   message text
#
# becomes::
#
#   On day month etc, Blah blah wrote:
#   > message text
#
# It's not meant to alter the contents of other peoples' messages, just to
# filter the topmost message so that when you start replying, you get a nice
# basis to start from.
require 'date'
require 'pp'

message = ARGF.read
# split into two parts at the first reply delimiter
# match group so leaves the delim in the array,
# this gets stripped away in the FieldRegex if's else clause
msgparts = message.split(/(---*[\w\s]+---*|______*)/)
# first bit is what we've written so far
mymsg = msgparts.slice!(0)
# rest is the quoted message
theirmsg = msgparts.join
# this regex separates message header field name from field content
FieldRegex = /^\s*(.+?):\s*(.+)$/
from = nil
date = nil
theirbody = []
theirmsg.lines do |line|
  if !from || !date
    if FieldRegex =~ line
      parts = line.scan(FieldRegex)
      if !from
        from = parts.first.last
      elsif !date
        begin
          DateTime.parse(parts.first.last)
          date = parts.first.last
        rescue ArgumentError
          # not a parseable date.. let's just fail
          date = " "
        end
      end
    else
      # ignore non-field, this strips extra message delims for example
    end
  else
    theirbody << line.gsub(/^/, "> ").gsub(/> >/, ">>")
  end
end

puts mymsg
puts "On #{date}, #{from} wrote:\n"
puts theirbody.join("")
