import ConfigParser
from os.path import expanduser
from twython import Twython
from tumblpy import Tumblpy

### News source
class NewsSource(object):
    def __init__(self, config, section):
        self.config = config
        self.section = section

    def login(self):
        config = self.config
        section = self.section

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
                config.set(section, "auth_token", authorized_tokens['oauth_token'])
                config.set(section, "auth_token_secret", authorized_tokens['oauth_token_secret'])
                save_config()

        return self.connect(
            app_key = the_app_key,
            app_secret = the_app_secret,
            oauth_token = config.get(section, "oauth_token"),
            oauth_token_secret = config.get(section, "oauth_token_secret") )

class TumblrNewsSource(NewsSource):
    def connect(self, app_key = None, app_secret = None, oauth_token = None, oauth_token_secret = None):
        return Tumblpy(app_key = app_key,
                       app_secret = app_secret,
                       oauth_token = oauth_token,
                       oauth_token_secret = oauth_token_secret )

class TwitterNewsSource(NewsSource):
    def connect(self, app_key = None, app_secret = None, oauth_token = None, oauth_token_secret = None):
        return Twython(twitter_token = app_key,
                       twitter_secret = app_secret,
                       oauth_token = oauth_token,
                       oauth_token_secret = oauth_token_secret )

def create_NewsSource(kind,config,section):
    if kind == 'Twitter':
        return TwitterNewsSource(config, section)
    elif kind == 'Tumblr':
        return TumblrNewsSource(config, section)
    else:
        return None
        
### Configuration
config_path = expanduser("~/.tw.ini")
def save_config ():
    with open(config_path, 'w') as config_fd:
        config.write(config_fd)

config = ConfigParser.RawConfigParser()
config.read(config_path)

### GO!
import datetime
import PyRSS2Gen

sources = [ create_NewsSource(kind,config,section) for section, kind in config.items("sources")]

tw1 = TwitterNewsSource(config, "twitter1").login()
tw2 = TwitterNewsSource(config, "twitter2").login()

results = tw1.getHomeTimeline(count = 20)

def tweet2rss(t):
    tweet_body = "@%s: %s" % (t['user']['screen_name'], t['text'])
    return PyRSS2Gen.RSSItem(
             title = tweet_body,
             link = "http://www.twitter.com/%s/status/%s" % (t['user']['screen_name'], t['id']),
             description = tweet_body,
             guid = str(t['id']),
             pubDate = t['created_at'])

rss = PyRSS2Gen.RSS2(
    title = "@%s/following" % (config.get("twitter1", "user")),
    description = "@%s following timeline" % (config.get("twitter1", "user")),
    link = "http://www.twitter.com/%s" % (config.get("twitter1", "user")),
    lastBuildDate = datetime.datetime.utcnow(),
    items = map(tweet2rss, results))

xml_path = "%s/example.rss" % expanduser(config.get("general", "output_dir"))
rss.write_xml(open(xml_path, "w"))

tu = TumblrNewsSource(config, "tumblr").login()
posts = tu.get('user/dashboard', params = {'offset': 20})['posts']
print len(posts)

# XXX Both:
# XXXX Remember last entry, get them all since then, produce an rss feed
