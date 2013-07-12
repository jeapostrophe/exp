from os.path import expanduser
from twython import Twython
from tumblpy import Tumblpy
import time
import ConfigParser
import datetime
import PyRSS2Gen

### News source
class NewsSource(object):
    def login(self, config, section):
        the_app_key = config.get(section, "app_key")
        the_app_secret = config.get(section, "app_secret")

        if not config.has_option(section, "oauth_token"):
            if not config.has_option(section, "auth_verifier"):
                t = self.connect(app_key = the_app_key,
                                 app_secret = the_app_secret )
                auth_props = t.get_authentication_tokens()
                print "Go to this URL: %s" % auth_props['auth_url']
                print "Then, add the verifier to the config file as the option auth_verifier under section %s" % section
                config.set(section, "auth_token", auth_props['oauth_token'])
                config.set(section, "auth_token_secret", auth_props['oauth_token_secret'])
                save_config()
                exit(0)

            t = self.connect(
                app_key = the_app_key,
                app_secret = the_app_secret,
                oauth_token = config.get(section, "auth_token"),
                oauth_token_secret = config.get(section, "auth_token_secret") )
            authorized_tokens = t.get_access_token(config.get(section, "auth_verifier"))
            config.set(section, "oauth_token", authorized_tokens['oauth_token'])
            config.set(section, "oauth_token_secret", authorized_tokens['oauth_token_secret'])
            save_config()

        return self.connect(
            app_key = the_app_key,
            app_secret = the_app_secret,
            oauth_token = config.get(section, "oauth_token"),
            oauth_token_secret = config.get(section, "oauth_token_secret") )

def append_map(f, l):
    out = []
    for e in l:
        time.sleep(1)
        out = out + f(e)
    return out

class Tumblr(NewsSource):
    def connect(self, app_key = None, app_secret = None, oauth_token = None, oauth_token_secret = None):
        return Tumblpy(app_key = app_key,
                       app_secret = app_secret,
                       oauth_token = oauth_token,
                       oauth_token_secret = oauth_token_secret )

    def rss(self, config, section):
        t = self.login(config, section)
        def inner(page_n):
            print "\tDownloading page %d" % page_n
            return t.get('user/dashboard', params = {'limit': 20, 'offset': page_n * 20})['posts']
        results = append_map(inner, range(4))
        return PyRSS2Gen.RSS2(
            title = "%s dashboard" % (config.get(section, "user")),
            description = "%s dashboard" % (config.get(section, "user")),
            link = "http://www.tumblr.com/dashboard",
            lastBuildDate = datetime.datetime.utcnow(),
            items = map(tumblr2rss, results))

class Twitter(NewsSource):
    def connect(self, app_key = None, app_secret = None, oauth_token = None, oauth_token_secret = None):
        return Twython(app_key, app_secret, oauth_token, oauth_token_secret )

    def rss(self, config, section):
        t = self.login(config, section)
        def inner(page_n):
            print "\tDownloading page %d" % page_n
            return t.get_home_timeline(count = 200, page = page_n)
        results = append_map(inner, range(4))
        return PyRSS2Gen.RSS2(
            title = "@%s/following" % (config.get(section, "user")),
            description = "@%s following timeline" % (config.get(section, "user")),
            link = "http://www.twitter.com/%s" % (config.get(section, "user")),
            lastBuildDate = datetime.datetime.utcnow(),
            items = map(tweet2rss, results))

def tumblr2rss(t):
    if t['type'] == 'text':
        return PyRSS2Gen.RSSItem(
            title = t['title'],
            author = t['blog_name'],
            link = t['post_url'],
            description = t['body'],
            guid = str(t['id']),
            pubDate = t['date'])
    elif t['type'] == 'answer':
        return PyRSS2Gen.RSSItem(
            title = "%s: %s" % (t['asking_name'], t['question']),
            author = t['blog_name'],
            link = t['post_url'],
            description = 
             """<p><a href="%s">%s</a>: %s</p><p>%s</p>""" %
             (t['asking_name'], t['asking_url'], t['question'], t['answer']),
            guid = str(t['id']),
            pubDate = t['date'])
    elif t['type'] == 'audio':
        return PyRSS2Gen.RSSItem(
            title = t['caption'],
            author = t['blog_name'],
            link = t['post_url'],
            description = "",
            guid = str(t['id']),
            pubDate = t['date'])
    elif t['type'] == 'video':
        return PyRSS2Gen.RSSItem(
            title = t['caption'],
            author = t['blog_name'],
            link = t['post_url'],
            description = "",
            guid = str(t['id']),
            pubDate = t['date'])
    elif t['type'] == 'link':
        return PyRSS2Gen.RSSItem(
            title = t['title'],
            author = t['blog_name'],
            link = t['post_url'],
            description = 
             """<p><a href="%s">%s</a></p><p>%s</p>""" %
             (t['url'], t['title'], t['description']),
            guid = str(t['id']),
            pubDate = t['date'])
    elif t['type'] == 'photo':
        return PyRSS2Gen.RSSItem(
            title = t['caption'],
            author = t['blog_name'],
            link = t['post_url'],
            description = 
             "<br/>".join(map((lambda photo:
                                   """<img src="%s" /> %s""" % 
                               (photo['alt_sizes'][0]['url'],
                                photo['caption'])),
                              t['photos'])),
            guid = str(t['id']),
            pubDate = t['date'])
    else:
        raise ValueError("Cannot RSS-ify Tumblr type %s" % t['type'])

def tweet2rss(t):
    tweet_body = "@%s: %s" % (t['user']['screen_name'], t['text'])
    return PyRSS2Gen.RSSItem(
        title = tweet_body,
        author = t['user']['screen_name'],
        link = "http://www.twitter.com/%s/status/%s" % (t['user']['screen_name'], t['id']),
        description = tweet_body,
        guid = str(t['id']),
        pubDate = t['created_at'])

### Configuration
config_path = expanduser("~/.tw.ini")
def save_config ():
    with open(config_path, 'w') as config_fd:
        config.write(config_fd)

config = ConfigParser.RawConfigParser()
config.read(config_path)

### GO!
for section, kind in config.items("sources"):
    print "Download source %s" % section
    ns = eval("%s()" % kind)
    time.sleep(1)
    rss = ns.rss(config, section)
    xml_path = "%s/%s-%s.rss" % (expanduser(config.get("general", "output_dir")), section, (config.get(section, "user")))
    rss.write_xml(open(xml_path, "w"))

